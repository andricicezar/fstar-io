let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-25.11";
  pkgs = import nixpkgs {
    config = {
      allowUnfreePredicate = pkg: (pkg.pname or "") == "claude-code";
    };
    overlays = [];
  };
  lib = pkgs.lib;
  system = pkgs.stdenv.hostPlatform.system;
  fstar = builtins.getFlake "github:FStarLang/FStar";
  claudeCode = builtins.getFlake "github:sadjow/claude-code-nix";
  imageTag =
    let value = builtins.getEnv "IMAGE_TAG";
    in if value == "" then "latest" else value;
  userName = "agent";
  userUid = 1000;
  userGid = 1000;
  repoDir = builtins.path {
    path = ../.;
    name = "project-repo";
  };

  writablePaths = [
    "/workspace/.git"
    "/workspace/seiostar/README.md"
    "/workspace/seiostar/Backtranslation.fst"
    "/workspace/seiostar/Compilation.fst"
    "/workspace/seiostar/IOStar.DestructLemmas.fst"
    "/workspace/seiostar/LambdaIO.ConstructLemmas.fst"
    "/workspace/seiostar/LambdaIO.DestructLemmas.fst"
    "/workspace/seiostar/LogRel.Semantics.fst"
    "/workspace/seiostar/LogRelSourceTarget.fst"
    "/workspace/seiostar/LogRelSourceTarget.CompatibilityLemmas.fst"
    "/workspace/seiostar/LogRelTargetSource.fst"
    "/workspace/seiostar/LogRelTargetSource.CompatibilityLemmas.fst"
    "/workspace/seiostar/QTypes.HelperTactics.fst"
    "/workspace/seiostar/QTypes.Subst.fst"
    "/workspace/seiostar/QTypes.TypEnv.fst"
    "/workspace/seiostar/Metaprogram.fst"
    "/workspace/seiostar/Metaprogram.Utils.fst"
    "/workspace/seiostar/RrHP.fst"
    "/workspace/seiostar/RunningExample.fst"
  ];

  makeWritableCommand = path:
    let
      relativePath = lib.removePrefix "/" (lib.removeSuffix "/" path);
      quotedPath = lib.escapeShellArg relativePath;
    in
    ''
      if [ -d ${quotedPath} ]; then
        chown -R ${toString userUid}:${toString userGid} ${quotedPath}
        chmod -R u+w ${quotedPath}
      elif [ -e ${quotedPath} ]; then
        chown ${toString userUid}:${toString userGid} ${quotedPath}
        chmod u+w ${quotedPath}
       fi
    '';

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
    claudeCode.packages.${system}."claude-code-bun"
  ];
in
pkgs.dockerTools.buildLayeredImage {
  name = "seiostar";
  tag = imageTag;

  contents = runtimePackages;

  config = {
    Entrypoint = [ "/workspace/seiostar/claude-sandbox.entrypoint.sh" ];
    Cmd = [ "/bin/bash" ];
    Env = [
      "PATH=/bin"
      "HOME=/home/${userName}"
      "BUILD_DIR=/tmp/seiostar_build"
      "SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt"
      "NIX_SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt"
      "CURL_CA_BUNDLE=/etc/ssl/certs/ca-certificates.crt"
      "NODE_EXTRA_CA_CERTS=/etc/ssl/certs/ca-certificates.crt"
    ];
    User = "agent";
    WorkingDir = "/workspace/seiostar";
  };

  extraCommands = ''
    mkdir -p bin etc home/${userName} tmp workspace
    cp -r ${repoDir}/. workspace/
    chmod 0755 workspace/seiostar/claude-sandbox.entrypoint.sh

    printf 'root:x:0:0:root:/root:/bin/bash\n${userName}:x:${toString userUid}:${toString userGid}:${userName}:/home/${userName}:/bin/bash\n' > etc/passwd
    printf 'root:x:0:\n${userName}:x:${toString userGid}:\n' > etc/group

    chmod 0755 home/${userName}
    chmod 1777 tmp
  '';

  fakeRootCommands = ''
    chown ${toString userUid}:${toString userGid} home/${userName}

    chmod u+w workspace/seiostar

    chmod -R u+w workspace/seiostar/.build
    rm -rf workspace/seiostar/.build

    # allow the agent to modify only specific files in the project
    ${lib.concatMapStringsSep "\n" makeWritableCommand writablePaths}
    chmod u-w workspace/seiostar # agent cannot create/remove files
  '';
}