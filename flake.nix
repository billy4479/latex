{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells.default = pkgs.mkShell {
        packages = with pkgs; [
          act
        ];
        nativeBuildInputs = with pkgs; [
          texliveFull # TODO: This can probably be reduced

          # `minted` dependencies
          python3
          python3Packages.pygments
        ];
      };
    });
}
