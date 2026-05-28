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

      cleanSrc =
        pkgs:
        pkgs.lib.cleanSourceWith {
          src = ./.;
          filter =
            path: type:
            let
              bn = baseNameOf (toString path);
            in
            !(builtins.elem bn [
              "_build"
              ".direnv"
              ".claude"
              "context"
              "result"
            ])
            && !(pkgs.lib.hasPrefix "Scratch" bn)
            && !(pkgs.lib.hasSuffix ".agdai" bn)
            && !(pkgs.lib.hasSuffix "~" bn)
            && !(pkgs.lib.hasPrefix "#" bn)
            && !(pkgs.lib.hasPrefix ".#" bn);
        };
    in
    {
      devShells = forEachSystem (pkgs: {
        default = pkgs.mkShell {
          packages = with pkgs; [
            (agda.withPackages (ps: [ ps.standard-library ]))
          ];
        };
      });

      packages = forEachSystem (pkgs: {
        default = pkgs.stdenvNoCC.mkDerivation {
          pname = "type-slicing";
          version = "0.1.0";
          src = cleanSrc pkgs;

          nativeBuildInputs = [ pkgs.agda ];

          buildPhase = ''
            runHook preBuild

            # Agda rewrites stdlib interfaces during checking; nix store is read-only.
            stdlib="$NIX_BUILD_TOP/stdlib"
            cp -r ${pkgs.agdaPackages.standard-library} "$stdlib"
            chmod -R u+w "$stdlib"

            cat > "$NIX_BUILD_TOP/libraries" <<EOF
            $stdlib/standard-library.agda-lib
            EOF

            mkdir -p "$out"
            set +e
            agda \
              --library-file="$NIX_BUILD_TOP/libraries" \
              -W error --double-check \
              all.agda 2>&1 | tee "$out/build.log"
            status=''${PIPESTATUS[0]}
            set -e

            ts=$(date -u +%FT%TZ)
            if [ "$status" -eq 0 ]; then
              printf 'PASS  agda exit=0  %s\n' "$ts" > "$out/status"
            else
              printf 'FAIL  agda exit=%s  %s\n' "$status" "$ts" > "$out/status"
            fi
            runHook postBuild
          '';

          installPhase = ''
            runHook preInstall
            find . \( -name '*.agda' -o -name '*.agda-lib' -o -name '*.agdai' \) \
              -exec cp -p --parents -t "$out" {} +
            runHook postInstall
          '';

          LC_ALL = "C.UTF-8";

          meta = {
            description = "Type-check the Agda formalisation of type slicing";
          };
        };
      });

      checks = forEachSystem (pkgs: {
        default = self.packages.${pkgs.system}.default;
      });
    };
}
