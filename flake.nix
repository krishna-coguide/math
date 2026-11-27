{
  description = "math: Python, Markdown and Lean development shell with Prime Agent tooling";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
  };

  outputs =
    { nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          arch = if system == "x86_64-linux" then "x64" else "arm64";

          # The one Python: scientific and symbolic stack, tests. Add a package
          # here (not with pip) so every worktree and agent sees the same set.
          python = pkgs.python3.withPackages (
            ps: with ps; [
              numpy
              scipy
              sympy
              mpmath
              networkx
              pandas
              matplotlib
              z3-solver
              pytest
              hypothesis
              ipython
            ]
          );

          # Keeps Prime Agent on its latest GitHub release in $TOOLS_DIR. Runs on
          # shell entry: one request, a download only when the release tag
          # changed, and offline keeps what's there. Prebuilt; uses nix-ld.
          toolsUpdate = pkgs.writeShellApplication {
            name = "tools-update";
            runtimeInputs = with pkgs; [
              coreutils
              curl
              gnutar
              gzip
            ];
            text = ''
              mkdir -p "$TOOLS_DIR"
              cd "$TOOLS_DIR"

              # update NAME REPO ASSET  ({v} in ASSET is replaced by the version)
              update() {
                local name=$1 repo=$2 tag asset
                tag=$(curl -fsSI --max-time 5 -o /dev/null -w '%{redirect_url}' "https://github.com/$repo/releases/latest") || return 0
                tag=''${tag##*/}
                [[ -n $tag && $tag != "$(cat "$name/.version" 2>/dev/null)" ]] || return 0
                asset=''${3//\{v\}/''${tag#v}}
                rm -rf "$name.new" && mkdir "$name.new"
                if curl -fsSL --max-time 300 -o "$name.new/$asset" "https://github.com/$repo/releases/download/$tag/$asset"; then
                  tar xzf "$name.new/$asset" -C "$name.new" && rm "$name.new/$asset"
                  echo "$tag" >"$name.new/.version"
                  rm -rf "$name" && mv "$name.new" "$name"
                  echo "tools-update: $name $tag" >&2
                else
                  rm -rf "$name.new"
                fi
              }

              update prime-agent PrimeIntellect-ai/prime-agent "prime-agent-{v}-linux-${arch}.tar.gz"
            '';
          };

          # `prime`: runs Prime Agent directly on the host (no sandbox),
          # installing it first if needed.
          prime = pkgs.writeShellApplication {
            name = "prime";
            runtimeInputs = [ toolsUpdate ];
            text = ''
              prime_bin=$TOOLS_DIR/prime-agent/prime-agent
              [[ -x $prime_bin ]] || tools-update
              [[ -x $prime_bin ]] || { echo "prime: not installed and download failed" >&2; exit 1; }
              exec "$prime_bin" "$@"
            '';
          };
        in
        {
          default = pkgs.mkShell {
            packages = with pkgs; [
              # Python: the interpreter with its packages, lint/format, types.
              python
              ruff
              pyright
              uv # only for throwaway venvs on top of `python`; see UV_* below

              # Lean 4: elan installs the toolchain each Lake project pins in
              # its `lean-toolchain` (Mathlib needs an exact one), so nixpkgs'
              # lean4 is deliberately absent. `lean`, `lake` are elan proxies.
              elan

              # Markdown: lint, convert, and PDF via Typst or LaTeX.
              markdownlint-cli2
              pandoc
              typst

              # LaTeX: the whole TeX Live (LuaLaTeX, XeLaTeX, pdfLaTeX, latexmk,
              # biber/biblatex, chktex, latexindent, every CTAN package), so an
              # agent never needs to install a package. tex-fmt formats .tex.
              texliveFull
              tex-fmt
              texlab # LaTeX language server

              # Prime Agent (see `prime` above).
              toolsUpdate
              prime

              # Shell and repository tools, also inherited by agent tool processes.
              bashInteractive
              coreutils
              git
              ripgrep
              fd
              jq
              curl
              gnugrep
              gnused
              gawk
              findutils
              which
              unzip
              zip
              nixfmt

              # GitHub is the only remote service; everything else is local.
              gh # GitHub CLI
            ];

            shellHook = ''
              export TOOLS_DIR="''${XDG_DATA_HOME:-$HOME/.local/share}/math/tools"
              tools-update
              echo "math: $(python --version), elan $(elan --version | cut -d' ' -f2); run 'prime' to start Prime Agent"
            '';

            env = {
              # uv: never download a Python; use the shell's.
              UV_PYTHON_DOWNLOADS = "never";
              UV_PYTHON = "${python}/bin/python";
              # matplotlib: render to files, never open a window from agents.
              MPLBACKEND = "Agg";
              # gh: no update nags; never open a browser/pager from agents.
              GH_NO_UPDATE_NOTIFIER = "1";
            };
          };
        }
      );

      formatter = forAllSystems (system: nixpkgs.legacyPackages.${system}.nixfmt);
    };
}
