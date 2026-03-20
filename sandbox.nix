let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-25.11";
  pkgs = import nixpkgs {
    config = {
    };
    overlays = [];
  };
  lib = pkgs.lib;
  system = pkgs.stdenv.hostPlatform.system;
  fstar = builtins.getFlake "github:FStarLang/FStar";
  llmAgents = builtins.getFlake "github:numtide/llm-agents.nix";
  imageTag =
    let value = builtins.getEnv "IMAGE_TAG";
    in if value == "" then "latest" else value;
  userName = "agent";
  userUid = 1000;
  userGid = 1000;
  repoDir = builtins.path {
    path = ./.;
    name = "project-repo";
  };

  runtimePackages = [
    pkgs.bashInteractive
    pkgs.coreutils
    pkgs.curl
    pkgs.dockerTools.caCertificates
    pkgs.findutils
    pkgs.git
    pkgs.gnugrep
    pkgs.gnumake
    pkgs.less
    pkgs.which
    fstar.packages.${system}.fstar
    fstar.packages.${system}.z3
    llmAgents.packages.${system}.claude-code
    llmAgents.packages.${system}.copilot-cli
    llmAgents.packages.${system}.gemini-cli
  ];
in
pkgs.dockerTools.buildLayeredImage {
  name = "fstario";
  tag = imageTag;

  contents = runtimePackages;

  config = {
    Entrypoint = [ "/workspace/sandbox.entrypoint.sh" ];
    Cmd = [ "/bin/bash" ];
    Env = [
      "PATH=/bin"
      "HOME=/home/${userName}"
      "BUILD_DIR=/tmp/fstario_build"
      "SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt"
      "NIX_SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt"
      "CURL_CA_BUNDLE=/etc/ssl/certs/ca-certificates.crt"
      "NODE_EXTRA_CA_CERTS=/etc/ssl/certs/ca-certificates.crt"
    ];
    User = "agent";
    WorkingDir = "/workspace";
  };

  extraCommands = ''
    mkdir -p bin etc home/${userName} tmp workspace
    cp -r ${repoDir}/. workspace/
    chmod 0755 workspace/sandbox.entrypoint.sh

    printf 'root:x:0:0:root:/root:/bin/bash\n${userName}:x:${toString userUid}:${toString userGid}:${userName}:/home/${userName}:/bin/bash\n' > etc/passwd
    printf 'root:x:0:\n${userName}:x:${toString userGid}:\n' > etc/group

    chmod 0755 home/${userName}
    chmod 1777 tmp
  '';

  fakeRootCommands = ''
    chown ${toString userUid}:${toString userGid} home/${userName}
    chown -R ${toString userUid}:${toString userGid} workspace
    chmod -R u+w workspace
  '';
}
