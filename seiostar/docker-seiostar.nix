let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-25.11";
  pkgs = import nixpkgs { config = {}; overlays = []; };
  lib = pkgs.lib;
  system = pkgs.stdenv.hostPlatform.system;
  fstar = builtins.getFlake "github:FStarLang/FStar";
  userName = "agent";
  userUid = 1000;
  userGid = 1000;
  source = builtins.path {
    path = ./../.;
    name = "seiostar-source";
  };
  writablePaths = [
    "/workspace/seiostar/.depend.mk"
    "/workspace/seiostar/.cache/"
    "/workspace/seiostar/README.md"
  ];

  makeWritableCommand = path:
    let
      relativePath = lib.removePrefix "/" (lib.removeSuffix "/" path);
      quotedPath = lib.escapeShellArg relativePath;
      isDirectory = lib.hasSuffix "/" path;
    in
    ''
      if [ -d ${quotedPath} ]; then
        chown -R ${toString userUid}:${toString userGid} ${quotedPath}
        chmod -R u+w ${quotedPath}
      elif [ -e ${quotedPath} ]; then
        chown ${toString userUid}:${toString userGid} ${quotedPath}
        chmod u+w ${quotedPath}
      elif [ ${if isDirectory then "1" else "0"} -eq 1 ]; then
        mkdir -p ${quotedPath}
        chown -R ${toString userUid}:${toString userGid} ${quotedPath}
        chmod -R u+w ${quotedPath}
      else
        mkdir -p "$(dirname ${quotedPath})"
        touch ${quotedPath}
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
  name = "docker-seiostar";
  tag = "latest";

  contents = runtimePackages;

  config = {
    Cmd = [ "/bin/bash" ];
    Env = [
      "PATH=/bin"
      "HOME=/home/${userName}"
    ];
    User = userName;
    WorkingDir = "/workspace/seiostar";
  };

  extraCommands = ''
    mkdir -p etc home/${userName} tmp workspace
    cp -r ${source}/. workspace/

    printf 'root:x:0:0:root:/root:/bin/bash\n${userName}:x:${toString userUid}:${toString userGid}:${userName}:/home/${userName}:/bin/bash\n' > etc/passwd
    printf 'root:x:0:\n${userName}:x:${toString userGid}:\n' > etc/group

    chmod 0755 home/${userName}
    chmod 1777 tmp
  '';

  fakeRootCommands = ''
    chattr +a workspace/seiostar
    chown ${toString userUid}:${toString userGid} home/${userName}
    ${lib.concatMapStringsSep "\n" makeWritableCommand writablePaths}
  '';
}