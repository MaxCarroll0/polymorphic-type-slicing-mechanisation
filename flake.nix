{
  description = "Agda Type Slicing — dev shell and type-check build";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-25.11";
  };

  outputs =
    { self, nixpkgs, ... }:
    let
      forEachSystem =
        f:
        nixpkgs.lib.genAttrs nixpkgs.lib.systems.flakeExposed (system: f nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forEachSystem (pkgs: {
        default = pkgs.mkShell {
          packages = with pkgs; [
            (agda.withPackages (ps: [ ps.standard-library ]))
          ];
        };
      });

      packages = forEachSystem (
        pkgs:
        let
          tsAgda = pkgs.tree-sitter.buildGrammar {
            language = "agda";
            version = "0.0.0+e8d47a6";
            src = pkgs.fetchFromGitHub {
              owner = "tree-sitter";
              repo = "tree-sitter-agda";
              rev = "e8d47a6987effe34d5595baf321d82d3519a8527";
              hash = "sha256-5h56+A7ZypckJ9mwht7XP/66oiehwAEQ4Z6WeVhQBvQ=";
            };
          };
          tsAgdaLib = pkgs.linkFarm "treesit-agda-lib" [
            {
              name = "libtree-sitter-agda${pkgs.stdenv.hostPlatform.extensions.sharedLibrary}";
              path = "${tsAgda}/parser";
            }
          ];
          ghcWithTS = pkgs.haskellPackages.ghcWithPackages (p: [ p.hs-tree-sitter ]);
        in
        {
          default = pkgs.stdenvNoCC.mkDerivation {
            pname = "type-slicing";
            version = "0.1.0";
            src = ./.;

            nativeBuildInputs = [ pkgs.agda ghcWithTS ];

          buildPhase = ''
            runHook preBuild

            # Agda rewrites stdlib interfaces during checking; nix store is read-only.
            stdlib="$NIX_BUILD_TOP/stdlib"
            cp -r ${pkgs.agdaPackages.standard-library} "$stdlib"
            chmod -R u+w "$stdlib"

            cat > "$NIX_BUILD_TOP/libraries" <<EOF
            $stdlib/standard-library.agda-lib
            EOF

            results="$out/TYPECHECK_RESULTS"
            mkdir -p "$results"
            set +e
            agda \
              --library-file="$NIX_BUILD_TOP/libraries" \
              -W error \
              all.agda 2>&1 | tee "$results/build.log"
            status=''${PIPESTATUS[0]}
            set -e

            ts=$(date -u +%FT%TZ)
            if [ "$status" -eq 0 ]; then
              printf 'PASS  agda exit=0  %s\n' "$ts" > "$results/status"
            else
              printf 'FAIL  agda exit=%s  %s\n' "$status" "$ts" > "$results/status"
            fi

            cp ${./scripts/scan-postulates-and-holes.hs} "$NIX_BUILD_TOP/Scan.hs"
            ghc -O -tmpdir "$NIX_BUILD_TOP" -odir "$NIX_BUILD_TOP" -hidir "$NIX_BUILD_TOP" \
              -L${tsAgdaLib} -ltree-sitter-agda \
              -optl-Wl,-rpath,${tsAgdaLib} \
              "$NIX_BUILD_TOP/Scan.hs" -o "$NIX_BUILD_TOP/scan-postulates-and-holes"
            "$NIX_BUILD_TOP/scan-postulates-and-holes" . > "$results/postulates_and_holes.txt"
            runHook postBuild
          '';

          installPhase = ''
            runHook preInstall
            mkdir -p "$out/out"
            find . \( -name '*.agda' -o -name '*.agda-lib' -o -name '*.agdai' \) \
              -exec cp -p --parents -t "$out/out" {} +
            runHook postInstall
          '';

          LC_ALL = "C.UTF-8";

          meta = {
            description = "Type-check the Agda formalisation of type slicing";
          };
          };
        }
      );

      checks = forEachSystem (pkgs: {
        default = self.packages.${pkgs.system}.default;
      });
    };
}
