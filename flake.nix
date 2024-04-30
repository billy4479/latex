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
      devShells.default = let
        fonts = with pkgs; [
          fira-code
          ubuntu_font_family
          fg-virgil # excalidraw font
        ];

        # https://discourse.nixos.org/t/project-local-fonts/22174/2?u=billy4479
        # https://github.com/Leixb/latex-template/blob/274df8a3cf8641906f32eef114f8fcf2d496936e/build-document.nix#L34
        fontDir = pkgs.symlinkJoin {
          name = "fonts";
          paths = fonts;
        };
      in
        pkgs.mkShell {
          nativeBuildInputs = with pkgs;
            [
              texliveFull # TODO: This can probably be reduced

              # `minted` dependencies
              python3
              python3Packages.pygments

              inkscape # `svg` dependencies
            ]
            ++ fonts;

          OSFONTDIR = "${fontDir}/share/fonts";
          FONTCONFIG_FILE = pkgs.makeFontsConf {
            fontDirectories = fonts;
          };
        };
    });
}
