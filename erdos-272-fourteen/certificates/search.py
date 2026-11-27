"""Find a finite case tree. No color or case split here is trusted by Lean."""

import ctypes as ct
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Iterator

import numpy as np

from audit import N, LIMIT, is_ap


def indices(bits: int) -> Iterator[int]:
    while bits:
        one = bits & -bits
        yield one.bit_length() - 1
        bits ^= one


def pack(bits: np.ndarray) -> int:
    return int.from_bytes(np.packbits(bits, bitorder="little").tobytes(), "little")


@dataclass
class Cut:
    tag: str
    work: int = 1
    value: int = 0
    children: tuple["Cut", "Cut"] | None = None


def split(tag: str, value: int, yes: Cut, no: Cut) -> Cut:
    return Cut(tag, 1 + yes.work + no.work, value, (yes, no))


RANK = Cut("rank")


class Search:
    def __init__(self, library: Path, cap: int, bound: int):
        self.bound = bound
        self.cap = cap
        self.coloring = ct.CDLL(str(library)).color_api
        self.coloring.argtypes = [
            ct.POINTER(ct.c_int32),
            ct.c_int,
            ct.c_int,
            ct.c_int,
            ct.c_int,
            ct.POINTER(ct.c_uint8),
        ]
        self.coloring.restype = ct.c_int
        self.masks = np.arange(LIMIT, dtype=np.int32)
        self.ap = np.array([is_ap(a) for a in range(LIMIT)])
        aps = list(map(int, np.flatnonzero(self.ap)))
        self.positive = [a for a in aps if a.bit_count() == 7] + [
            a for a in aps if a.bit_count() == 11
        ]
        self.zero = [a for a in aps if a.bit_count() in (9, 10, 13)]
        self.zero_bits = sum(1 << a for a in self.zero)
        self.sup = [pack((self.masks & p) == p) for p in self.positive]
        self.trace = [
            pack(self.ap[self.masks & p] | ((self.masks & p) == 0))
            for p in self.positive
        ]
        self.omit = [pack((self.masks & (1 << i)) == 0) for i in range(N)]
        self.active = [
            sum(1 << i for i, p in enumerate(self.positive) if a & p == p)
            for a in range(LIMIT)
        ]
        self.nontrivial = pack(np.array([a.bit_count() >= 2 for a in range(LIMIT)]))

    @lru_cache(maxsize=None)
    def neighbors(self, a: int) -> int:
        return pack(self.ap[self.masks & a]) & ~(1 << a)

    def auto(self, pool: int, required: int) -> bool:
        return (
            92
            + sum(bool(pool & s) for s in self.sup)
            + min(self.cap, (pool & self.zero_bits).bit_count())
            <= self.bound
            or any(not (pool & self.sup[j]) for j in indices(required))
            or any(not (pool & omit) for omit in self.omit)
        )

    def paint(
        self, free: int, selected: tuple[int, ...]
    ) -> tuple[list[int], Cut] | None:
        k = self.bound - len(selected)
        colors: dict[int, int] = {}
        bad: list[int] = []
        remaining = free
        for color in range(k):
            available = remaining
            while available:
                one = available & -available
                v = one.bit_length() - 1
                available = (available ^ one) & ~self.neighbors(v)
                remaining ^= one
                colors[v] = color
            if remaining.bit_count() <= k - color - 1:
                for j, v in enumerate(indices(remaining), color + 1):
                    colors[v] = j
                break
        else:
            vertices = np.fromiter(indices(free), dtype=np.int32)
            out = np.empty(len(vertices), np.uint8)
            found = self.coloring(
                vertices.ctypes.data_as(ct.POINTER(ct.c_int32)),
                len(vertices),
                k,
                1500 if len(vertices) < 800 else 600,
                0,
                out.ctypes.data_as(ct.POINTER(ct.c_uint8)),
            )
            if not found:
                return None
            colors = {int(v): int(c) for v, c in zip(vertices, out)}
            if found < 0:
                bad = [v for v, c in colors.items() if c == 255]
                for v in bad:
                    del colors[v]
        for j, v in enumerate(selected, k):
            colors[v] = j
        classes: list[list[int]] = [[] for _ in range(self.bound)]
        for v in sorted(colors):
            classes[colors[v]].append(v)
        digits = [d for group in classes for d in [len(group), *group]]
        encoded = 0
        for d in reversed(digits):
            encoded = (encoded << N) | d
        return bad, Cut("paint", len(colors), encoded)

    def refine(self, pool: int, required: int, selected: tuple[int, ...]) -> Cut:
        if self.auto(pool, required):
            return RANK
        missing = required
        common = LIMIT - 1
        free = pool
        for a in selected:
            missing &= ~self.active[a]
            common &= a
            free &= ~(1 << a)
        painted = self.paint(free, selected)
        if painted is not None and not painted[0]:
            return painted[1]
        # A large family must meet every active-token witness pool and miss every
        # common point. Its rank cost also requires enough actual zero-weight APs.
        demands = [(pool & self.sup[j], 1) for j in indices(missing)]
        demands += [(pool & self.omit[i], 1) for i in indices(common)]
        zneed = (
            self.bound
            + 1
            - 92
            - sum(bool(pool & s) for s in self.sup)
            - sum(a in self.zero for a in selected)
        )
        if zneed > 0:
            demands.append((free & self.zero_bits, zneed))
        choices: list[int] = []
        rest = RANK
        if demands:
            group, need = min(demands, key=lambda g: g[0].bit_count() - g[1])
            size = group.bit_count() - need + 1
            if size <= 50:
                choices = sorted(
                    indices(group),
                    key=lambda v: ((pool & self.neighbors(v)).bit_count(), v),
                )[:size]
        if painted is not None and (not choices or len(painted[0]) < len(choices)):
            choices, rest = painted
        if choices:
            yes_cases: list[tuple[int, Cut]] = []
            for v in choices:
                one = 1 << v
                yes = self.refine(
                    (pool & self.neighbors(v)) | one, required, selected + (v,)
                )
                yes_cases.append((v, yes))
                pool &= ~one
            if rest is RANK and not self.auto(pool, required):
                raise RuntimeError("uncovered branch")
            for v, yes in reversed(yes_cases):
                rest = split("mem", v, yes, rest)
            return rest
        v = min(indices(free), key=lambda a: (pool & self.neighbors(a)).bit_count())
        one = 1 << v
        return split(
            "mem",
            v,
            self.refine((pool & self.neighbors(v)) | one, required, selected + (v,)),
            self.refine(pool & ~one, required, selected),
        )

    def support_tree(self, support: list[int]) -> Cut:
        pool = self.nontrivial
        known = 0
        for a in support:
            pool &= self.neighbors(a) | (1 << a)
            known |= self.active[a]

        def visit(pool: int, req: int, open_bits: int) -> Cut:
            if self.auto(pool, req):
                return RANK
            options = [j for j in indices(open_bits) if pool & self.sup[j]]
            if pool.bit_count() > 750 and options:
                j = max(options, key=lambda i: (pool & ~self.trace[i]).bit_count())
                left = open_bits ^ (1 << j)
                return split(
                    "tok",
                    self.positive[j],
                    visit(pool & self.trace[j], req | (1 << j), left),
                    visit(pool & ~self.sup[j], req, left),
                )
            return self.refine(pool, req, tuple(support))

        tree = visit(pool, 0, ((1 << len(self.positive)) - 1) & ~known)
        return self.exclude_trivial(tree)

    @staticmethod
    def exclude_trivial(node: Cut) -> Cut:
        for a in reversed([0] + [1 << i for i in range(N)]):
            node = split("mem", a, RANK, node)
        return node

    def tree(self) -> Cut:
        # First distinguish the least pair or triple, if any. Counts are
        # computed on the full pool; the selected mask is not an assumption of Safe.
        def visit(pool: int, req: int, selected: tuple[int, ...], untested: int) -> Cut:
            if self.auto(pool, req):
                return RANK
            options = [j for j in indices(untested) if pool & self.sup[j]]
            if not options:
                return self.refine(pool, req, selected)
            if pool.bit_count() <= 2400:
                free = pool & ~sum(1 << a for a in selected)
                painted = self.paint(free, selected)
                if painted is not None:
                    bad, leaf = painted
                    if not bad:
                        return leaf
                    if len(bad) <= 2:
                        return self.refine(pool, req, selected)
            j = max(options, key=lambda i: (pool & ~self.trace[i]).bit_count())
            later = untested ^ (1 << j)
            return split(
                "tok",
                self.positive[j],
                visit(pool & self.trace[j], req | (1 << j), selected, later),
                visit(pool & ~self.sup[j], req, selected, later),
            )

        all_tokens = (1 << len(self.positive)) - 1
        small = sorted(
            (a for a in range(LIMIT) if 2 <= a.bit_count() <= 3),
            key=lambda a: (a.bit_count(), a),
        )
        pool = self.nontrivial
        yes = []
        for a in small:
            yes.append(
                (a, visit(pool & (self.neighbors(a) | (1 << a)), 0, (a,), all_tokens))
            )
            pool &= ~(1 << a)
        node = visit(pool, 0, (), all_tokens)
        for a, child in reversed(yes):
            node = split("mem", a, child, node)
        return self.exclude_trivial(node)
