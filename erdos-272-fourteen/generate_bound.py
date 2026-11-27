"""Generate independently checkable Lean modules for the unrestricted upper bound.

Run from any directory with the repository's Nix-shell Python, then run
`lake build Erdos272Bounds` from the project directory. No network or solver
certificate is trusted: every generated leaf is checked inside Lean.
"""

import json
import os
from pathlib import Path
import subprocess

from certificates.search import BOUND, Cut, Search


def term(node: Cut) -> str:
    if node.tag == "rank":
        return ".rank"
    if node.tag == "paint":
        return f"(.paint 0x{node.value:x})"
    assert node.children is not None
    left, right = node.children
    return f"(.{node.tag} {node.value} {term(left)} {term(right)})"


def write_forest(
    source: Path,
    name: str,
    cap: int,
    trees: list[tuple[str, Cut]],
) -> None:
    package = source / "Erdos272Bounds" / name
    package.mkdir(parents=True, exist_ok=True)
    module = f"Erdos272Bounds.{name}"
    ns = f"E272.Search.Run{BOUND}.{name}"
    definitions: list[str] = []
    leaves: list[str] = []
    joins: list[str] = []
    serial = 0
    # Zero allowance is conditional until the two forests are joined.
    binder = f" (rk : RankBound {BOUND} 0)" if cap == 0 else ""
    rk = "rk" if cap == 0 else f"(rankBoundFour {BOUND})"

    def emit(node: Cut, pool: str, req: str) -> str:
        nonlocal serial
        key = serial
        serial += 1
        cut = f"cut{key}"
        if node.work < 2000 or node.children is None:
            proof = f"verified {cap} {BOUND} {pool} {req} {term(node)} {rk} (by decide +kernel)"
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
        dest.append(f"theorem {cut}{binder} : Safe {BOUND} {pool} {req} := {proof}")
        return f"({cut} rk)" if cap == 0 else cut

    roots = [emit(tree, pool, "[]") for pool, tree in trees]
    if cap == 0:
        joins.append(f"theorem bounded{binder} : Safe {BOUND} board [] := {roots[0]}")
    else:
        joins.append(
            f"theorem bounded : ∀ s ∈ Neutral.kernelSupports, Safe {BOUND} (seeded s) [] := by\n"
            "  simp only [Neutral.kernelSupports, List.forall_mem_cons]\n"
            + "  exact ⟨"
            + ", ".join(roots)
            + ", List.forall_mem_nil _⟩"
        )
    write_module(package / "States.lean", ns, ["Erdos272.Certificate"], definitions)
    # Each forest is independent of the other. Four parts each let Lake check
    # both forests concurrently without changing any mathematical assumptions.
    count = 4
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
    if cap:
        imports.append("Erdos272.KernelSupports")
    write_module(package.with_suffix(".lean"), ns, imports, joins)
    print(f"Generated {len(leaves)} blocks for {name}.")


def write_module(path: Path, ns: str, imports: list[str], body: list[str]) -> None:
    text = (
        "".join(f"import {module}\n" for module in imports) + f"namespace {ns}\n"
        "set_option Elab.async false\nset_option maxRecDepth 64000\nset_option maxHeartbeats 0\n"
        + "\n".join(body)
        + f"\nend {ns}\n"
    )
    if not path.exists() or path.read_text() != text:
        path.write_text(text)


def main() -> None:
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
    subprocess.run(["lake", "build", "Erdos272.KernelSupports"], cwd=root, check=True)
    output = subprocess.check_output(
        ["lake", "env", "lean", "--run", "certificates/PrintSupports.lean"],
        cwd=root,
        text=True,
    )
    supports: list[list[int]] = json.loads(output)
    support_search = Search(library, 4)
    write_forest(
        source,
        "Patterns",
        4,
        [(f"(seeded {s})", support_search.support_tree(s)) for s in supports],
    )
    write_forest(source, "Cases", 0, [("board", Search(library, 0).tree())])
    write_module(
        source / "Erdos272Bounds.lean",
        f"E272.Search.Run{BOUND}",
        [
            "Erdos272Bounds.Patterns",
            "Erdos272Bounds.Cases",
            "Erdos272.SupportRank",
            "Erdos272",
        ],
        [
            f"theorem rankAbove{BOUND} : RankBound {BOUND} 0 := by\n"
            "  intro F hf hn hlarge\n"
            "  rcases Neutral.rank_or_kernel_support F hf hn with hr | ⟨s, hs, hm⟩\n"
            "  · simpa using hr\n"
            "  · exact False.elim ((not_le_of_gt hlarge) (Patterns.bounded s hs F hf hn (seeded_covers hf hm) (by simp)))",
            f"theorem upper{BOUND} (F : Finset Mask) (hf : Valid F) : F.card ≤ {BOUND} := by\n"
            "  by_cases h : 96 ≤ F.card\n"
            f"  · exact Cases.bounded rankAbove{BOUND} F hf (nonstar_of_large hf h) (fun a _ => board_bit a) (by simp)\n"
            "  · omega",
            f"#print axioms upper{BOUND}",
        ],
    )
    print("Run `lake build Erdos272Bounds` to check the unrestricted theorem.")


if __name__ == "__main__":
    main()
