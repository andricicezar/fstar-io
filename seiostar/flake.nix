{
  description = "Development shell for the seiostar artifact";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    fstar = {
      url = "github:FStarLang/FStar";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { nixpkgs, fstar, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in {
      devShells = forAllSystems (system:
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
        });
    };
}