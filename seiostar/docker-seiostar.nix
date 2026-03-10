let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-25.11";
  pkgs = import nixpkgs { config = {}; overlays = []; };
  system = pkgs.stdenv.hostPlatform.system;
  fstar = builtins.getFlake "github:FStarLang/FStar";
  source = builtins.path {
    path = ./../.;
    name = "seiostar-source";
  };

  runtimePackages = [
    pkgs.bashInteractive
    pkgs.coreutils
    pkgs.gnumake
    fstar.packages.${system}.fstar
    fstar.packages.${system}.z3
  ];
in
pkgs.dockerTools.buildLayeredImage {
  name = "docker-seiostar";
  tag = "latest";

  contents = runtimePackages;

  config = {
    Cmd = [ "/bin/bash" ];
    Env = [
      "PATH=/bin"
    ];
    WorkingDir = "/workspace/seiostar";
  };

  extraCommands = ''
    mkdir -p workspace
    cp -r ${source}/. workspace/
  '';
}