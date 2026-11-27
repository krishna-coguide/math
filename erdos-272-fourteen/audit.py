"""Independent exact counts and optional regeneration of the rooted covers."""

from argparse import ArgumentParser
from itertools import combinations
from math import comb, gcd

N = 14
LIMIT = 1 << N
Bucket = tuple[int, int, int]


def points(mask: int) -> list[int]:
    return [i for i in range(N) if mask & (1 << i)]


def is_ap(mask: int) -> bool:
    xs = points(mask)
    return bool(xs) and len({b - a for a, b in zip(xs, xs[1:])}) <= 1


def hull(mask: int) -> int:
    xs = points(mask)
    step = gcd(*(p - xs[0] for p in xs[1:]))
    return sum(1 << p for p in range(xs[0], xs[-1] + 1, step))


def rooted_cover(root: int, aps: set[int]) -> list[Bucket]:
    small = [a for a in range(LIMIT) if a & (1 << root) and a.bit_count() <= 3]
    bent = [a for a in small if a not in aps]
    large = sorted(a for a in aps if a & (1 << root) and a.bit_count() >= 4)
    match: dict[int, int] = {}

    def augment(p: int, seen: set[int]) -> bool:
        for t in bent:
            if t & p != t or t in seen:
                continue
            seen.add(t)
            if t not in match or augment(match[t], seen):
                match[t] = p
                return True
        return False

    for p in large:
        augment(p, set())
    cover = [(match.get(t, t), t, hull(t)) if t in bent else (t, 0, 0) for t in small]
    return cover + [(p, 0, 0) for p in large if p not in match.values()]


def audit(emit: bool) -> None:
    aps = {a for a in range(1, LIMIT) if is_ap(a)}
    sevens = [a for a in aps if a.bit_count() == 7]
    long = [a for a in range(1, LIMIT) if any(a & p == p for p in sevens)]
    long_aps = set(long) & aps
    penalties = [a for a in aps if a.bit_count() in (3, 4, 6)]

    def score(a: int) -> int:
        k = a.bit_count()
        return 1 + comb(k, 2) - k - sum(a & p == p for p in penalties)

    rare = sorted(a for a in range(1, LIMIT) if a not in aps and score(a) <= 0)
    print(f"APs: {len(aps)}; seven-term APs: {len(sevens)}")
    print(f"Masks containing a seven-term AP: {len(long)}")
    print(f"Special list: {len(long_aps)} long APs + {len(rare)} nonprogressions")
    print(
        "Unordered pairs with long AP intersection:",
        sum((a & b) in long_aps for a, b in combinations(long, 2)),
    )
    covers = [rooted_cover(x, aps) for x in range(N)]
    print("Rooted cover sizes:", [len(c) for c in covers])
    if emit:
        for i, cs in enumerate(covers):
            print(
                f"palette{i}: [" + ", ".join(f"⟨{p},{t},{h}⟩" for p, t, h in cs) + "]"
            )


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument(
        "--palettes", action="store_true", help="print the Lean bucket data"
    )
    audit(parser.parse_args().palettes)
