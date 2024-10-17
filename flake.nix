{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        fonts = with pkgs; [
          (nerdfonts.override { fonts = [ "FiraCode" ]; })
          ubuntu_font_family
          fg-virgil # excalidraw font
        ];

        # https://discourse.nixos.org/t/project-local-fonts/22174/2?u=billy4479
        # https://github.com/Leixb/latex-template/blob/274df8a3cf8641906f32eef114f8fcf2d496936e/build-document.nix#L34
        fontDir = pkgs.symlinkJoin {
          name = "fonts";
          paths = fonts;
        };

        # https://raw.githubusercontent.com/NixOS/nixpkgs/master/pkgs/tools/typesetting/tex/texlive/tlpdb.nix
        # https://nixos.org/manual/nixpkgs/stable/#sec-language-texlive
        # https://discourse.nixos.org/t/new-tex-live-withpackages-function/34902/16
        texPkgs = pkgs.texliveSmall.withPackages (
          ps: with ps; [
            latexmk
            latexindent
            texcount

            # Direct dependencies
            dirtytalk
            tcolorbox
            tikzfill
            enumitem
            doclicense
            cancel
            minted
            svg
            physics
            rsfs
            lipsum
            cleveref
            thmtools
            siunitx
            subfig
            emoji
            multicol

            # Indirect dependencies
            environ
            pdfcol
            xifthen
            ifmtarg
            xstring
            ccicons
            csquotes
            upquote
            transparent
            hyperxmp
            luacode
          ]
        );

        nativeBuildInputs =
          (with pkgs; [
            texPkgs

            # `minted` dependencies
            python3
            python3Packages.pygments
            which

            inkscape # `svg` dependencies
          ])
          ++ fonts;

        OSFONTDIR = "${fontDir}/share/fonts";
        FONTCONFIG_FILE = pkgs.makeFontsConf { fontDirectories = fonts; };

        OUTDIR = "build"; # This is not optimal as it needs to be changed manually in minted and svg preamble
      in
      {
        devShells.default = pkgs.mkShell { inherit nativeBuildInputs OSFONTDIR FONTCONFIG_FILE; };
        packages = rec {
          document = pkgs.stdenvNoCC.mkDerivation {
            name = "latex-documents";
            src = ./.;

            inherit nativeBuildInputs OSFONTDIR FONTCONFIG_FILE;

            TEXMFVAR = "./cache/var";
            TEXMFHOME = "./cache";

            buildPhase = ''
              runHook preBuild

              latexmk -lualatex -shell-escape -auxdir=${OUTDIR}/aux -outdir=${OUTDIR} -interaction=nonstopmode *.tex

              runHook postBuild
            '';

            installPhase = ''
              runHook preInstall

              mkdir -p $out
              cp ${OUTDIR}/*.pdf $out

              runHook postInstall
            '';
          };
          default = document;
        };
      }
    );
}
