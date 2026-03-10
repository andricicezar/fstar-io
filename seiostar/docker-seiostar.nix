let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-25.11";
  pkgs = import nixpkgs { config = {}; overlays = []; };
  lib = pkgs.lib;
  system = pkgs.stdenv.hostPlatform.system;
  fstar = builtins.getFlake "github:FStarLang/FStar";
  readIntEnv = name: default:
    let
      value = builtins.getEnv name;
    in
    if value == "" then default
    else if builtins.match "[0-9]+" value != null then builtins.fromJSON value
    else throw "${name} must be a non-negative integer";
  imageTag =
    let value = builtins.getEnv "IMAGE_TAG";
    in if value == "" then "latest" else value;
  userName = "agent";
  userUid = readIntEnv "GIT_UID" 1000;
  userGid = readIntEnv "GIT_GUID" 1000;
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
    pkgs.git
    pkgs.gnumake
    pkgs."util-linux"
    fstar.packages.${system}.fstar
    fstar.packages.${system}.z3
  ];
in
pkgs.dockerTools.buildLayeredImage {
  name = "seiostar";
  tag = imageTag;

  contents = runtimePackages;

  config = {
    Entrypoint = [ "/bin/seiostar-entrypoint" ];
    Cmd = [ "/bin/bash" ];
    Env = [
      "PATH=/bin"
      "HOME=/home/${userName}"
      "BUILD_DIR=/tmp/seiostar_build"
    ];
    User = "root";
    WorkingDir = "/workspace/seiostar";
  };

  extraCommands = ''
    mkdir -p bin etc home/${userName} tmp workspace
    cp -r ${repoDir}/. workspace/

    cat > bin/seiostar-entrypoint <<'EOF'
    #!/bin/bash
    set -euo pipefail

    if [ "$(id -u)" -eq 0 ]; then
      if [ -e /workspace/.git ]; then
        chown -R ${toString userUid}:${toString userGid} /workspace/.git
      fi

      exec /bin/setpriv \
        --reuid=${toString userUid} \
        --regid=${toString userGid} \
        --clear-groups \
        /bin/seiostar-entrypoint "$@"
    fi

    found=0
    while IFS= read -r dir; do
      if [ "$dir" = "/workspace" ]; then
        found=1
        break
      fi
    done < <(git config --global --get-all safe.directory 2>/dev/null || true)

    if [ "$found" -eq 0 ]; then
      git config --global --add safe.directory /workspace
    fi

    exec "$@"
    EOF

    printf 'root:x:0:0:root:/root:/bin/bash\n${userName}:x:${toString userUid}:${toString userGid}:${userName}:/home/${userName}:/bin/bash\n' > etc/passwd
    printf 'root:x:0:\n${userName}:x:${toString userGid}:\n' > etc/group

    chmod 0755 bin/seiostar-entrypoint
    chmod 0755 home/${userName}
    chmod 1777 tmp
  '';

  fakeRootCommands = ''
    chown ${toString userUid}:${toString userGid} home/${userName}
    chown ${toString userUid}:${toString userGid} workspace
    chmod u+w workspace

    chmod u+w workspace/seiostar
    chmod -R u+w workspace/seiostar/.build
    rm -rf workspace/seiostar/.build

    # allow the agent to modify only specific files in the project
    ${lib.concatMapStringsSep "\n" makeWritableCommand writablePaths}
    chmod u-w workspace/seiostar # agent cannot create/remove files
  '';
}