let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-25.11";
  pkgs = import nixpkgs { config = {}; overlays = []; };
  imageTag =
    let value = builtins.getEnv "IMAGE_TAG";
    in if value == "" then "latest" else value;
  lib = pkgs.lib;
  system = pkgs.stdenv.hostPlatform.system;
  fstar = builtins.getFlake "github:FStarLang/FStar";
  userName = "agent";
  userUid = 1000;
  userGid = 1000;
  repoDir = builtins.path {
    path = ../.;
    name = "project-repo";
  };

  writablePaths = [ 
    "/workspace/seiostar/README.md"
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
    pkgs.gnumake
    fstar.packages.${system}.fstar
    fstar.packages.${system}.z3
  ];
in
pkgs.dockerTools.buildLayeredImage {
  name = "seiostar";
  tag = imageTag;

  contents = runtimePackages;

  config = {
    Cmd = [ "/bin/bash" ];
    Env = [
      "PATH=/bin"
      "HOME=/home/${userName}"
      "BUILD_DIR=/tmp/seiostar_build"
    ];
    User = userName;
    WorkingDir = "/workspace/seiostar";
  };

  extraCommands = ''
    mkdir -p etc home/${userName} tmp workspace
    cp -r ${repoDir}/. workspace/

    printf 'root:x:0:0:root:/root:/bin/bash\n${userName}:x:${toString userUid}:${toString userGid}:${userName}:/home/${userName}:/bin/bash\n' > etc/passwd
    printf 'root:x:0:\n${userName}:x:${toString userGid}:\n' > etc/group

    chmod 0755 home/${userName}
    chmod 1777 tmp
  '';

  fakeRootCommands = ''
    chown ${toString userUid}:${toString userGid} home/${userName}
    chmod u+w workspace/seiostar

    # allow the agent to modify only specific files in the project
    ${lib.concatMapStringsSep "\n" makeWritableCommand writablePaths}
    chmod u-w workspace/seiostar # agent cannot create/remove files
  '';
}