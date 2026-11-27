# math Agent Operating Contract

## Mission and authority

This repository is for mathematics: notes in Markdown, papers and longer
write-ups in LaTeX, formal proofs in Lean 4, and computation and experiments
in Python. It runs fully
locally; GitHub is the only remote service.

Act like an owner. Finish the requested outcome, repair problems you find in
scope, and prefer evidence over assumptions. The user owns the choice of
problems, definitions, and conventions. A subagent must not quietly turn a
finding into one of those decisions.

Instructions are ordered by authority: the user and applicable `AGENTS.md`, then
an approved plan, then task handoffs. A global skill may strengthen a workflow
but never weaken this contract.

## Repository layout: bare repo and worktrees

```text
 /home/dev/math/                 bare repository (git worktree list: bare)
   .prime/<initiative-id>/       plans, notes, reports; local, never in git
   worktrees/                    git's worktree metadata (do not edit)
   main/                         worktree on branch main
   <initiative-id>/              a worktree for one piece of work
   <initiative-id>-<task>/       a lane worktree for one task of it
```

- Start Prime Agent from the bare repo root (`/home/dev/math`) so its artifacts
  land in `.prime/`, outside every worktree. Enter the dev shell from a
  worktree (`nix develop ./main`, or `cd main && nix develop`).
- `git` commands in the bare root act on the repository. Commands that need a
  work tree (status, add, commit, diff) run in a worktree or with
  `git -C <worktree>`.
- Resolve the active root with `git rev-parse --show-toplevel`.

### Worktree usage

- Every piece of work happens in its own worktree. Never commit directly in
  `main/` except a merge of reviewed work or a fetch-and-merge of the remote.
- Branch names match the worktree directory: kebab-case, lowercase. A
  lane branch is `<initiative-id>-<task>`, not `<initiative-id>/<task>`: git
  cannot hold a branch `a/b` next to a branch `a`.
- Create a worktree from an exact base:

  ```bash
  cd /home/dev/math
  git -C main fetch origin main
  git -C main merge --no-gpg-sign FETCH_HEAD
  git -C main worktree add -b <initiative-id> ../<initiative-id> "$(git -C main rev-parse HEAD)"
  ```

  A lane branches from its initiative's worktree:
  `git -C <initiative-id> worktree add -b <initiative-id>-<task> ../<initiative-id>-<task> <base-sha>`.
- `FETCH_HEAD` is per worktree. A fetch in the bare root does not fill a
  worktree's `FETCH_HEAD`. Fetch and merge in the same worktree, as above.
  Inspect its location with `git rev-parse --git-path FETCH_HEAD`.
- Preserve diverged local commits with a normal merge. Never reset, rebase, or
  force-push them away.
- One branch can be checked out in only one worktree. To look at another
  branch read-only, use `git show <branch>:<path>` or a detached worktree
  (`git worktree add --detach <path> <sha>`).
- Lake builds (`.lake/`) are per worktree, so a fresh worktree of a Mathlib
  project needs `lake exe cache get` before `lake build`
  ([Lean](#lean)).
- Remove a worktree only when its branch is merged and the worktree is clean
  (`git status --short` is empty): `git worktree remove <path>`, then
  `git branch -d <branch>`. Run `git worktree prune` if a directory was deleted
  by hand. Never use `--force` on a worktree holding work you did not verify
  is merged.

### GitHub

`origin` is `https://github.com/krishna-coguide/math` (private). Git
authenticates through `gh` (`credential.https://github.com.helper` in the bare
repo's config); `gh auth status` shows the account. Never print or copy the
token.

- Push a branch: `git push -u origin <branch>`.
- Reviewed work lands through a pull request:
  `gh pr create --base main --head <branch> --title "<summary>" --body "<what and how it was checked>"`,
  then `gh pr merge <n> --merge` when the user approves. Afterwards
  fetch-and-merge in `main/`.
- Pushing to `main`, merging a PR, deleting a remote branch, and changing repo
  settings or visibility are external actions: do them only with clear
  authority each time. Never force-push.

## Workspace, safety, and secrets

- Work only in the assigned worktree unless the user explicitly authorizes
  another location.
- Inspect `git status --short` before work. Preserve unrelated tracked,
  untracked, ignored, and concurrent-agent changes. Never use reset, clean,
  checkout-overwrite, or force operations to erase work you do not own.
- Never put secrets, tokens, or credentials in files, logs, plans, memories, or
  commits. Do not read or print ignored local configuration.
- Do not commit large generated output: Lake builds, PDFs, plots, caches, or
  data files, unless the user asks for a specific artifact to be versioned.
  Commit the source that regenerates it.
- Do not commit copyrighted papers or book excerpts beyond short quotations
  with citation.
- Keep diffs coherent and scoped.

## Durable knowledge and memory

Improve the repository's operating knowledge as you work.

- When you verify a lasting procedure, tool behavior, or non-obvious invariant
  future contributors need, update this `AGENTS.md` in the same coherent change.
  Keep it source-backed, concise, and general. Do not record transient task
  facts.
- Record recurring papercuts, workarounds, and process lessons in
  project-scoped memory. Log every memory about this project in project-local
  memory, never global memory; global memory is only for user preferences that
  apply across repositories.
- Correct stale memories when new evidence disproves them. Never store secrets,
  speculative claims, or temporary branch state in memory.

## Working style

- Every nontrivial task keeps a todo list from intake to handoff: observable
  outcomes, dependencies, validation, honest confidence. Update it when
  evidence or scope changes.
- For a large or ambiguous initiative, write the requirements and a plan to
  `.prime/<initiative-id>/` before implementing, and get the user's approval
  for definitions, statements of theorems, and scope. A plan names the exact
  files, definitions, statements, lemmas, and checks.
- Use subagents when parallelism adds speed or confidence: independent
  literature or Mathlib searches, separate lemmas in separate lane worktrees,
  numerical experiments, adversarial review of a proof or a plan. Give each a
  bounded outcome, exact scope and exclusions, base revision, and the checks to
  run. Do not spawn agents to fill slots or to duplicate an investigation.
- A shared worktree has one active writer. Others may read and review only.
- Every nontrivial change gets an independent review before it merges
  ([Commit and review protocol](#commit-and-review-protocol)).

## Mathematical standards

- Label every claim by its status, and never upgrade it without the evidence:
  - **formalized**: a Lean proof that builds, with no `sorry`, checked with
    `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`);
  - **proved**: a complete written proof in the notes;
  - **checked numerically**: Python evidence, with the range, precision,
    and method stated;
  - **conjecture** or **heuristic**: everything else.
- Numerical evidence is not a proof. Say what was computed, over what inputs,
  with what arithmetic (floating point, `mpmath` at a stated precision, exact
  `sympy`/integer/rational), and what could break it.
- Cite sources for known results: author, title, and theorem or section
  number; a URL or DOI where there is one; for Mathlib, the declaration name.
- State definitions and conventions before using them (indexing from 0 or 1,
  `ℕ` including 0, normalizations of transforms, and similar). Keep a statement
  in the notes and its Lean statement in agreement; when they differ, say how.
- Do not change a theorem statement, definition, or hypothesis to make a proof
  go through without the user's approval. Report that the original is false or
  stuck, with the counterexample or the obstruction.

## Development environment

The agent runs inside the flake's dev shell, so its environment is exactly
`flake.nix` (the `default` shell) plus the host. Enter it from a worktree:

```bash
nix develop
```

It provides:

- **Python**: one interpreter (`python`) with `numpy`, `scipy`, `sympy`,
  `mpmath`, `networkx`, `pandas`, `matplotlib`, `z3-solver`, `pytest`,
  `hypothesis`, `ipython`; `ruff` (lint, format), `pyright` (types); `uv`.
- **Lean 4**: `elan`, with `lean` and `lake` as elan proxies.
- **Markdown**: `markdownlint-cli2`, `pandoc`, `typst`.
- **LaTeX**: all of TeX Live (`lualatex`, `xelatex`, `pdflatex`, `latexmk`,
  `biber`/biblatex, `chktex`, `latexindent`, every CTAN package); `tex-fmt`;
  `texlab`.
- **Tools**: `git`, `gh`, `ripgrep`, `fd`, `jq`, `curl`, `zip`/`unzip`,
  `nixfmt`, coreutils and friends; Prime Agent (`prime`, `tools-update`).

Rules:

- Need a tool or Python package? Add it to `flake.nix` (a Python package goes
  in `python3.withPackages`) in its own `nix:` commit; do not `pip install`
  into the user's environment. A one-off experiment may use
  `uv venv --system-site-packages` in an ignored `.venv/`; nothing committed
  may depend on it.
- `UV_PYTHON_DOWNLOADS=never` and `UV_PYTHON` point uv at the shell's Python.
  `MPLBACKEND=Agg`: matplotlib writes files, never opens a window.
- An agent keeps the shell it started in. After a `flake.nix` or `flake.lock`
  change, check from that worktree with
  `nix develop -c bash -c '<commands>'`.
- Shell entry runs `tools-update` (latest Prime Agent release, not pinned by
  `flake.lock`) into `${XDG_DATA_HOME:-~/.local/share}/math/tools`. `prime`
  runs it unsandboxed on the host.

Flake maintenance:

```bash
nix flake check --all-systems
nix fmt -- --check flake.nix
nix flake update nixpkgs        # deliberately, then review and commit flake.lock
```

## Python

- Scripts and modules are plain Python 3 with type hints; deterministic (fix
  seeds and print them); runnable from the worktree root.
- Use exact arithmetic (`sympy`, `fractions`, integers) or `mpmath` at a
  stated precision when a result's correctness depends on it; floats only
  when error is bounded and the tolerance reasoning is written down.
- Tests use `pytest`; property tests use `hypothesis`. A test of a numerical
  routine checks known values, edge inputs, and states its tolerance.
- Figures go to files (PNG or SVG) next to the notes that use them, made by a
  committed script.

## Lean

- Each Lake project pins its toolchain in `lean-toolchain`; elan installs it on
  first use into `~/.elan` (shared by all worktrees). Never hand-edit
  `lean-toolchain` independently of Mathlib: Mathlib needs the exact toolchain
  its release names.
- New Mathlib project: `lake +leanprover-community/mathlib4:lean-toolchain new <Name> math`.
  Update Mathlib deliberately (`lake update mathlib`, then copy
  Mathlib's `lean-toolchain`), in its own `deps:` commit.
- Before building a Mathlib project in a fresh worktree, run
  `lake exe cache get` to download prebuilt `.olean`s; never build Mathlib
  from source. `.lake/` is ignored.
- Search before proving: `exact?`, `apply?`, `rw?`, `simp?`, and `rg` over
  `.lake/packages/mathlib/Mathlib`. Reuse Mathlib names and conventions.
- `sorry` is allowed only on a work-in-progress branch and is listed in the
  handoff. Nothing merged to `main` contains `sorry`, `admit`, or a new
  `axiom`, unless the user approved it and it is recorded under
  [Known debts](#known-debts-and-claims-you-must-not-overstate).
- A formalized result's handoff includes `#print axioms <name>` output.

## Markdown

- Math typesetting: full GitHub-compatible MathJax is allowed (GitHub renders
  Markdown math with MathJax). Use any of GitHub's math syntaxes:
  - inline `$...$`, or ``$`...`$`` when the expression contains characters
    Markdown would otherwise interpret (`_`, `*`, `\`, `|`);
  - display `$$...$$` on its own lines, or a fenced ` ```math ` block;
  - any command or environment GitHub's MathJax supports (`aligned`, `cases`,
    `pmatrix`, `\operatorname`, `\mathbb`, `\tag`, and so on).

  Write for GitHub's renderer: no LaTeX packages, no `\newcommand`
  shared across blocks, and no raw HTML for math. Check a note on GitHub
  (or in the PR's rich diff) when its math is complex. Material that needs
  real LaTeX (packages, theorem environments, TikZ, a bibliography) is a
  `.tex` document instead ([LaTeX](#latex)).
- One idea per paragraph; headings for structure; definitions, statements, and
  proofs clearly marked (`**Theorem.**`, `**Proof.**`, ending with ∎).
- Link a note to the Lean declaration and Python script that back it, by
  repository path.
- PDF: read the note as GitHub Markdown (`-f gfm`) so all the math syntaxes
  above parse. Through LaTeX (best math), or through Typst (fast; Pandoc's
  Typst template needs an explicit font, and Typst bundles New Computer
  Modern):

  ```bash
  pandoc -f gfm note.md -o note.pdf --pdf-engine=lualatex
  pandoc -f gfm note.md -o note.pdf --pdf-engine=typst -V mainfont="New Computer Modern"
  ```

## LaTeX

- Modern LaTeX: compile with LuaLaTeX through latexmk; UTF-8 source;
  `unicode-math` for fonts (not `inputenc`/`fontenc`); `amsmath`, `amsthm`,
  `mathtools`; `biblatex` with the `biber` backend (not BibTeX); `hyperref`
  then `cleveref` (loaded last) for references. Prefer `\(...\)` and
  `\[...\]` or `equation`/`align` over `$$...$$`.
- Every TeX Live package is already installed; never use `tlmgr`.
- Build, from the document's directory, with output kept out of the source:

  ```bash
  latexmk -lualatex -interaction=nonstopmode -halt-on-error -outdir=build <doc>.tex
  ```

  `build/` is ignored; commit the `.tex`, `.bib`, and figure sources, not the
  PDF, unless the user asks for it. A build is clean when the log has no
  undefined references or citations and no overfull boxes you did not accept.
- Lint with `chktex -q <doc>.tex`; format with `tex-fmt <doc>.tex`
  (`tex-fmt --check` in validation). Keep one sentence per line so diffs
  stay readable.
- Bibliography entries carry a DOI or URL where there is one.

## Validation

Run the checks relevant to the change, from the worktree root, inside the dev
shell:

```bash
git diff --check
markdownlint-cli2                          # globs, ignores: .markdownlint-cli2.jsonc
ruff check . && ruff format --check .
pyright
pytest
(cd <lake-project> && lake build)          # with no `sorry` warnings
latexmk -lualatex -halt-on-error -outdir=build <doc>.tex && chktex -q <doc>.tex && tex-fmt --check <doc>.tex
nix fmt -- --check flake.nix               # when flake.nix changed
```

Before handoff:

1. map each requirement to a concrete observed check;
2. inspect `git status --short` and the scoped diff;
3. run `git diff --check`;
4. check Markdown math, fences, and links when docs change;
5. confirm no secrets, generated output, debug code, `sorry`, unrelated paths,
   or accidental metadata entered the change;
6. state exactly what ran, its result, each claim's status
   ([Mathematical standards](#mathematical-standards)), and any gap.

Do not call substitute validation equivalent. A Lean file that was not built
is not formalized; a script that was not run is not evidence.

## Commit and review protocol

Commit completed work in the worktree. Always disable GPG signing:

```bash
git commit --no-gpg-sign -m "<lowercase-scope>: <imperative summary>"
```

Scopes: `notes:`, `tex:`, `lean:`, `py:`, `nix:`, `deps:`, `docs:` (this file, README),
or a topic name when it is clearer.

Before committing:

1. inspect `git status --short`, the scoped diff, and recent log;
2. stage only owned paths with `git add -- <paths>`;
3. inspect `git diff --cached --check` and the complete staged diff;
4. make one atomic concern per commit;
5. never stage `.prime/**`, `.lake/`, build output, or unrelated agent work.

A reviewer independently checks the commit or range against the request:
rebuilds the Lean, reruns the scripts and tests, reads each proof for gaps,
and returns findings ordered by severity with path, symbol or line, the
failure, and the required correction. A passing build does not excuse a
statement that says the wrong thing. Reviewers report findings and do not edit
unless reassigned as the worker.

## Known debts and claims you must not overstate

- None yet.

Add an entry when you find a debt that cannot be fixed now, with the
condition that retires it.
