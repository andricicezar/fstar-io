let
  flake = builtins.getFlake (toString ./.);
  system = builtins.currentSystem;
  hasDevShell =
    builtins.hasAttr "devShells" flake
    && builtins.hasAttr system flake.devShells
    && builtins.hasAttr "default" flake.devShells.${system};
  hasDefault =
    builtins.hasAttr "default" flake
    && builtins.hasAttr system flake.default;
in
if hasDevShell then
  flake.devShells.${system}.default
else if hasDefault then
  flake.default.${system}
else
  throw "flake.nix does not expose a default development shell for ${system}"
