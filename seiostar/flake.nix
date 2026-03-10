{
  description = "SEIO*";

  inputs = {
    flake-utils.url = "flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    fstar.url = "github:FStarLang/FStar";
  };

  outputs = { flake-utils, nixpkgs, fstar, ... }:
    flake-utils.lib.eachDefaultSystem (system: (
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in {
          default = pkgs.mkShellNoCC {
            inputsFrom = [
              fstar.devShells.${system}.default
            ];

            packages = [
              fstar.packages.${system}.fstar
              fstar.packages.${system}.z3
            ];

            GREETING = "Hello, Nix!";

            shellHook = ''
              echo "$GREETING"
            '';
          };
        }));
}