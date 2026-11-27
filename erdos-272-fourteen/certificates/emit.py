"""Split an exhaustive certificate into independently checked Lean modules."""

from pathlib import Path

from certificates.search import Cut, Search


def term(node: Cut) -> str:
    if node.tag == "rank":
        return ".rank"
    if node.tag == "paint":
        return f"(.paint 0x{node.value:x})"
    assert node.children is not None
    yes, no = node.children
    return f"(.{node.tag} {node.value} {term(yes)} {term(no)})"


def write_module(path: Path, ns: str, imports: list[str], body: list[str]) -> None:
    text = (
        "".join(f"import {module}\n" for module in imports) + f"namespace {ns}\n"
        "set_option Elab.async false\nset_option maxRecDepth 64000\nset_option maxHeartbeats 0\n"
        + "\n".join(body)
        + f"\nend {ns}\n"
    )
    if not path.exists() or path.read_text() != text:
        path.write_text(text)


def write_cases(source: Path, search: Search, tree: Cut, lanes: int) -> None:
    """The initial pool of each block is a literal. `member` and `token` must
    unify those literals with their exact successor pools when joining blocks.
    The search generator cannot introduce a subset or omit a branch this way.
    """
    from audit import LIMIT

    bound = search.bound
    ns = f"E272.Search.Run{bound}.Cases"
    package = source / "Erdos272Bounds/Cases"
    package.mkdir(parents=True, exist_ok=True)
    module = "Erdos272Bounds.Cases"
    anchors: list[str] = []
    joins: list[str] = []
    blocks: list[tuple[int, str, str, Cut]] = []
    serial = 0

    def partition(node: Cut, pool: int, req: str) -> str:
        nonlocal serial
        i = serial
        serial += 1
        name = f"pool{i}" if i else "board"
        if i:
            anchors.append(f"def {name} : Nat := 0x{pool:x}")
        if node.work <= 60000 or node.children is None:
            blocks.append((i, name, req, node))
            return f"Chunk{i}.bounded"
        a = node.value
        if node.tag == "tok":
            j = search.positive.index(a)
            y = partition(node.children[0], pool & search.trace[j], f"({a} :: {req})")
            n = partition(node.children[1], pool & ~search.sup[j], req)
            proof = f"token (P := {name}) (t := {a}) (by decide +kernel) {y} {n}"
        else:
            y = partition(
                node.children[0], pool & (search.neighbors(a) | (1 << a)), req
            )
            n = partition(node.children[1], pool & ~(1 << a), req)
            proof = f"member (P := {name}) {a} {y} {n}"
        joins.append(f"theorem join{i} : Safe {bound} {name} {req} := {proof}")
        return f"join{i}"

    root = partition(tree, (1 << LIMIT) - 1, "[]")
    write_module(package / "Anchors.lean", ns, ["Erdos272Bounds.Rank"], anchors)
    buckets: list[list[tuple[int, str, str, Cut]]] = [[] for _ in range(lanes)]
    loads = [0] * lanes
    for block in sorted(blocks, key=lambda b: b[3].work, reverse=True):
        j = loads.index(min(loads))
        buckets[j].append(block)
        loads[j] += block[3].work + 100

    def local(block: tuple[int, str, str, Cut]) -> list[str]:
        i, pool, req, t = block
        out = [f"namespace Chunk{i}"]
        k = 0

        def emit(node: Cut, p: str, r: str) -> str:
            nonlocal k
            ident = k
            k += 1
            if node.work < 3000 or node.children is None:
                proof = f"verified 0 {bound} {p} {r} {term(node)} rankAbove95 (by decide +kernel)"
            else:
                a = node.value
                op = "Token" if node.tag == "tok" else "Mem"
                lp, rp = f"y{ident}", f"n{ident}"
                out.extend(
                    [
                        f"private def {lp} := yes{op} {p} {a}",
                        f"private def {rp} := no{op} {p} {a}",
                    ]
                )
                yes = emit(
                    node.children[0], lp, f"({a} :: {r})" if node.tag == "tok" else r
                )
                no = emit(node.children[1], rp, r)
                proof = (
                    f"token (t := {a}) (by decide +kernel) {yes} {no}"
                    if node.tag == "tok"
                    else f"member {a} {yes} {no}"
                )
            nm = f"cut{ident}" if ident else "bounded"
            vis = "private " if ident else ""
            out.append(f"{vis}theorem {nm} : Safe {bound} {p} {r} := {proof}")
            return nm

        emit(t, pool, req)
        out.append(f"end Chunk{i}")
        return out

    tips = []
    for j, bucket in enumerate(buckets):
        prev = f"{module}.Anchors"
        g = 0
        body: list[str] = []
        work = 0
        for b in bucket:
            body.extend(local(b))
            work += b[3].work
            if work >= 130000:
                label = f"Lane{j}Group{g}"
                write_module(package / f"{label}.lean", ns, [prev], body)
                prev = f"{module}.{label}"
                g += 1
                body = []
                work = 0
        if body:
            label = f"Lane{j}Group{g}"
            write_module(package / f"{label}.lean", ns, [prev], body)
            prev = f"{module}.{label}"
        tips.append(prev)
    joins.insert(0, "set_option exponentiation.threshold 32768")
    joins.append(f"theorem bounded : Safe {bound} board [] := {root}")
    write_module(package.with_suffix(".lean"), ns, tips, joins)
    print(f"Generated {len(blocks)} Cases subtrees in {lanes} parallel lanes.")
