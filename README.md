# math

Mathematics in Markdown, LaTeX, Lean 4, and Python. Contributors and agents start
with [AGENTS.md](AGENTS.md).

## Layout

```text
 math/                  bare repository; start `prime` here
   main/                worktree on branch main (this checkout)
   <initiative-id>/     one worktree per piece of work
```

## Development shell

Requires Nix with `nix-command` and `flakes`. Supports x86-64 and ARM Linux.
From a worktree:

```sh
nix develop
```

It provides Python 3 with numpy, scipy, sympy, mpmath, networkx, pandas,
matplotlib, z3, pytest, hypothesis and IPython; ruff, pyright, uv; elan for
Lean 4 and Lake; markdownlint-cli2, Pandoc and Typst; all of TeX Live
(LuaLaTeX, latexmk, biber, chktex), tex-fmt and texlab; Git, GitHub CLI, the
usual shell tools, and Prime Agent (`prime`, `tools-update`). Everything runs
locally; GitHub is the only remote service.

## Prime Agent

Inside `nix develop`, run `prime` from the bare repo root
(`cd .. && prime`, or `prime -c` to resume). Shell entry runs `tools-update`,
which keeps Prime Agent on its latest GitHub release in
`${XDG_DATA_HOME:-~/.local/share}/math/tools`; offline keeps the installed
copy. It is not pinned by `flake.lock` and needs nix-ld on NixOS. `prime` is
**not sandboxed**: it has your user's access.

## Maintenance

```sh
nix flake check --all-systems
nix fmt -- --check flake.nix
nix flake update nixpkgs   # then review and commit flake.lock
```
