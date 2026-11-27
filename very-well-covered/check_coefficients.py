"""Verify the coefficient valley by counting independent sets with j old vertices."""

from math import comb

T = 192
N = 38 * T  # Number of old vertices; the other N vertices are leaves.


def independent_count(k: int) -> int:
    """Count independent k-sets of the leafy extension of the specified join."""
    leaves_only = comb(N, k)
    return leaves_only + sum(
        (comb(T, j) * 30**j + comb(4 * T, j) * 2**j) * comb(N - j, k - j)
        for j in range(1, min(k, 4 * T) + 1)
    )


def main() -> None:
    indices = (3738, 3789, 3840)
    counts = [independent_count(k) for k in indices]
    floors = [10**6 * count // 2 ** (42 * T) for count in counts]
    assert counts[0] > counts[1] < counts[2]
    assert floors == [9957, 9105, 9976]
    print("k     floor(10^6 * count / 2^(42t))")
    for k, value in zip(indices, floors, strict=True):
        print(f"{k}  {value}")


if __name__ == "__main__":
    main()
