"""Exact finite check of the hitting time index and every admissible fusion.

Run from the worktree root: python tree-hitting-time/check_trees.py --max-n 11
NetworkX supplies one representative of each isomorphism class of trees for
orders >= 2. All walk calculations use Python integers, not simulation.
"""

from argparse import ArgumentParser
from collections.abc import Iterator
from functools import cache
from itertools import combinations, permutations

import networkx as nx


def measurements(tree: nx.Graph) -> tuple[int, dict[int, int]]:
    """Compute directed hitting times from edge first steps; check the bridge."""

    @cache
    def edge(u: int, v: int) -> int:
        return len(tree[u]) + sum(edge(w, u) for w in tree[u] if w != v)

    n = len(tree)
    t: dict[int, int] = {}
    h: dict[tuple[int, int], int] = {}
    d: dict[tuple[int, int], int] = {}
    for u, paths in nx.all_pairs_shortest_path(tree):
        for v, path in paths.items():
            d[u, v] = len(path) - 1
            h[u, v] = sum(edge(x, y) for x, y in zip(path, path[1:]))
        t[u] = sum(d[u, v] for v in tree)
    for u in tree:
        for v in tree:
            assert h[u, v] == (n - 1) * d[u, v] + t[v] - t[u]
            if u != v:
                degree = len(tree[u])
                assert degree * h[u, v] == degree + sum(h[w, v] for w in tree[u])
    return sum(max(h[u, v], h[v, u]) for u, v in combinations(tree, 2)), t


def pendant_paths(tree: nx.Graph, b: int) -> Iterator[list[int]]:
    for start in tree[b]:
        prev, u = b, start
        path = [u]
        while len(tree[u]) == 2:
            prev, u = u, next(v for v in tree[u] if v != prev)
            path.append(u)
        if len(tree[u]) == 1:
            yield path


def check_order(n: int) -> tuple[int, int, int, int]:
    path_ht, _ = measurements(nx.path_graph(n))
    trees = [nx.path_graph(1)] if n == 1 else nx.nonisomorphic_trees(n)
    count = moves = corner = 0
    for tree in trees:
        assert isinstance(tree, nx.Graph)
        count += 1
        old, t = measurements(tree)
        nonpath = any(len(tree[u]) >= 3 for u in tree)
        assert old < path_ht if nonpath else old == path_ht
        found = False
        for b in tree:
            if len(tree[b]) < 3:
                continue
            for a, z in permutations(pendant_paths(tree, b), 2):
                p, q = len(a), len(z)
                c = n - p - q
                if p < q or c < p + 1:
                    continue
                found = True
                moves += 1
                graft = tree.copy()
                graft.remove_edge(b, a[0])
                graft.add_edge(z[-1], a[0])
                new, t_new = measurements(graft)
                assert new > old
                if (p, q, c) == (2, 1, 3):
                    corner += 1
                    tip_gap = t[a[-1]] - t[z[-1]]
                    new_gap = t_new[a[-1]] - t_new[z[-1]]
                    assert (tip_gap, new_gap - tip_gap) == (2, 4)
        assert nonpath == found
    return count, moves, corner, path_ht


def main() -> None:
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=11)
    limit = parser.parse_args().max_n
    if limit < 1:
        parser.error("--max-n must be positive")
    print("n trees admissible_ordered_fusions corner_fusions HT(path)")
    for n in range(1, limit + 1):
        print(n, *check_order(n))


if __name__ == "__main__":
    main()
