"""Generate independently checkable Lean modules for the unrestricted upper bound.

Run from any directory with the repository's Nix-shell Python, then run
`lake build Erdos272Bounds` from the project directory. No network or solver
certificate is trusted: every generated leaf is checked inside Lean.
"""

from argparse import ArgumentParser
import json
import os
from pathlib import Path
import subprocess

from certificates.emit import term, write_cases, write_module
from certificates.search import Cut, Search

BOUND = 95


def write_patterns(source: Path, trees: list[tuple[str, Cut]], lanes: int) -> None:
    name = "Patterns"
    package = source / "Erdos272Bounds" / name
    package.mkdir(parents=True, exist_ok=True)
    module = f"Erdos272Bounds.{name}"
    ns = f"E272.Search.Run{BOUND}.{name}"
    definitions: list[str] = []
    leaves: list[str] = []
    joins: list[str] = []
    serial = 0

    def emit(node: Cut, pool: str, req: str) -> str:
        nonlocal serial
        key = serial
        serial += 1
        cut = f"cut{key}"
        if node.work < 2000 or node.children is None:
            proof = f"verified 4 {BOUND} {pool} {req} {term(node)} (rankBoundFour {BOUND}) (by decide +kernel)"
            dest = leaves
        else:
            a = node.value
            suffix = "Token" if node.tag == "tok" else "Mem"
            ly, ln = f"bits{key}y", f"bits{key}n"
            for label, op in [(ly, "yes"), (ln, "no")]:
                definitions.append(f"def {label} : Nat := {op}{suffix} {pool} {a}")
            yes = emit(
                node.children[0], ly, f"({a} :: {req})" if node.tag == "tok" else req
            )
            no = emit(node.children[1], ln, req)
            proof = (
                f"token (t := {a}) (by decide +kernel) {yes} {no}"
                if node.tag == "tok"
                else f"member {a} {yes} {no}"
            )
            dest = joins
        dest.append(f"theorem {cut} : Safe {BOUND} {pool} {req} := {proof}")
        return cut

    roots = [emit(tree, pool, "[]") for pool, tree in trees]
    joins.append(
        f"theorem bounded : ∀ s ∈ Neutral.kernelSupports, Safe {BOUND} (seeded s) [] := by\n"
        "  simp only [Neutral.kernelSupports, List.forall_mem_cons]\n"
        + "  exact ⟨"
        + ", ".join(roots)
        + ", List.forall_mem_nil _⟩"
    )
    write_module(package / "States.lean", ns, ["Erdos272.Certificate"], definitions)
    # Independent batches affect build scheduling only.
    count = min(lanes, 12)
    batches: list[list[str]] = [[] for _ in range(count)]
    cost = [0] * count
    for leaf in sorted(leaves, key=len, reverse=True):
        i = cost.index(min(cost))
        batches[i].append(leaf)
        cost[i] += len(leaf) + 500
    imports = []
    for i, body in enumerate(batches):
        part = f"Part{i}"
        write_module(package / f"{part}.lean", ns, [f"{module}.States"], body)
        imports.append(f"{module}.{part}")
    imports.append("Erdos272.KernelSupports")
    write_module(package.with_suffix(".lean"), ns, imports, joins)
    print(f"Generated {len(leaves)} blocks for {name}.")


def main() -> None:
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--only", choices=("patterns", "cases"))
    parser.add_argument(
        "--lanes",
        type=int,
        default=32,
        help="concurrent Lean batches for the unrestricted case check",
    )
    args = parser.parse_args()
    if args.lanes < 1:
        parser.error("--lanes must be positive")
    root = Path(__file__).resolve().parent
    source = root / ".lake/proof-src"
    package = source / "Erdos272Bounds"
    package.mkdir(parents=True, exist_ok=True)
    library = source / "color.so"
    subprocess.run(
        [
            os.environ.get("CXX", "c++"),
            "-O3",
            "-std=c++20",
            "-fPIC",
            "-shared",
            str(root / "certificates/color.cpp"),
            "-o",
            str(library),
        ],
        check=True,
    )
    if args.only != "cases":
        subprocess.run(
            ["lake", "build", "Erdos272.KernelSupports"], cwd=root, check=True
        )
        output = subprocess.check_output(
            ["lake", "env", "lean", "--run", "certificates/PrintSupports.lean"],
            cwd=root,
            text=True,
        )
        supports: list[list[int]] = json.loads(output)
        support_search = Search(library, 4, BOUND)
        write_patterns(
            source,
            [(f"(seeded {s})", support_search.support_tree(s)) for s in supports],
            args.lanes,
        )
        write_module(
            source / "Erdos272Bounds/Rank.lean",
            "E272.Search",
            ["Erdos272.SupportRank", "Erdos272Bounds.Patterns"],
            [
                f"theorem rankAbove{BOUND} : RankBound {BOUND} 0 := by\n"
                "  intro F hf hn hlarge\n"
                "  rcases Neutral.rank_or_kernel_support F hf hn with hr | ⟨s, hs, hm⟩\n"
                "  · simpa using hr\n"
                f"  · exact False.elim ((not_le_of_gt hlarge) (Run{BOUND}.Patterns.bounded s hs F hf hn (seeded_covers hf hm) (by simp)))"
            ],
        )
    if args.only != "patterns":
        case_search = Search(library, 0, BOUND)
        write_cases(source, case_search, case_search.tree(), args.lanes)
    write_module(
        source / "Erdos272Bounds.lean",
        f"E272.Search.Run{BOUND}",
        [
            "Erdos272Bounds.Rank",
            "Erdos272Bounds.Cases",
            "Erdos272",
        ],
        [
            f"theorem upper{BOUND} (F : Finset Mask) (hf : Valid F) : F.card ≤ {BOUND} := by\n"
            "  by_cases h : 96 ≤ F.card\n"
            f"  · exact Cases.bounded F hf (nonstar_of_large hf h) (fun a _ => board_bit a) (by simp)\n"
            "  · omega",
            f"#print axioms upper{BOUND}",
        ],
    )
    print("Run `lake build Erdos272Bounds` to check the unrestricted theorem.")


if __name__ == "__main__":
    main()
