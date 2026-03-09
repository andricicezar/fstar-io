let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-25.11";
  pkgs = import nixpkgs { config = {}; overlays = []; };
  system = pkgs.stdenv.hostPlatform.system;
  fstar = builtins.getFlake "github:FStarLang/FStar";
in

pkgs.mkShellNoCC {
  inputsFrom = [
    fstar.devShells.${system}.default
  ];

  packages = [
    fstar.packages.${system}.fstar
    fstar.packages.${system}.z3
#    fstar.packages.${system}.emacs
  ];

  GREETING = "Hello, Nix!";

  shellHook = ''
    echo $GREETING
  '';
}
