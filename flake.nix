{
  description = "Agda Type Slicing Dev Env & Build";

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
          # create an environment with Agda with the standard library
          packages = with pkgs; [
            (agda.withPackages (ps: [
              ps.standard-library
            ]))
          ];

        };
      });
    };

  # TODO: Build
}
