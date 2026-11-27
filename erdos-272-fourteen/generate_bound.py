"""Generate independently checkable Lean modules for the unrestricted upper bound.

Run from any directory with the repository's Nix-shell Python, then run
`lake build Erdos272Bounds` from the project directory. No network or solver
certificate is trusted: every generated leaf is checked inside Lean.
"""

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


def declarations(tree: Cut) -> tuple[list[str], list[str], list[str]]:
    definitions: list[str] = []
    leaves: list[str] = []
    joins: list[str] = []
    serial = 0

    def emit(node: Cut, pool: str, req: str) -> str:
        nonlocal serial
        key = serial
        serial += 1
        name = f"cut{key}"
        if node.work < 2000 or node.children is None:
            proof = f"verified {BOUND} {pool} {req} {term(node)} (by decide +kernel)"
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
        dest.append(f"theorem {name} : Safe {BOUND} {pool} {req} := {proof}")
        return name

    root = emit(tree, "board", "[]")
    joins.append(f"theorem costSearch{BOUND} : Safe {BOUND} board [] := {root}")
    joins.append(
        f"theorem upper{BOUND} (F : Finset Mask) (hf : Valid F) : F.card ≤ {BOUND} := by\n"
        "  by_cases h : 96 ≤ F.card\n"
        f"  · exact costSearch{BOUND} F hf (nonstar_of_large hf h) (fun a _ => board_bit a) (by simp)\n"
        "  · omega"
    )
    joins.append(f"#print axioms upper{BOUND}")
    return definitions, leaves, joins


def write_module(path: Path, imports: list[str], body: list[str]) -> None:
    ns = f"E272.Search.Run{BOUND}"
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
    tree = Search(library).tree()
    definitions, leaves, joins = declarations(tree)
    write_module(package / "States.lean", ["Erdos272.Certificate"], definitions)
    # Splitting declarations is only scheduling: it does not split assumptions.
    count = 8
    batches: list[list[str]] = [[] for _ in range(count)]
    cost = [0] * count
    for leaf in sorted(leaves, key=len, reverse=True):
        i = cost.index(min(cost))
        batches[i].append(leaf)
        cost[i] += len(leaf) + 500
    modules = []
    for i, body in enumerate(batches):
        name = f"Part{i}"
        write_module(package / f"{name}.lean", ["Erdos272Bounds.States"], body)
        modules.append(f"Erdos272Bounds.{name}")
    write_module(source / "Erdos272Bounds.lean", modules + ["Erdos272"], joins)
    print(
        f"Generated {len(leaves)} certificate blocks for upper bound {BOUND}. "
        "Run `lake build Erdos272Bounds` to verify them."
    )


if __name__ == "__main__":
    main()
