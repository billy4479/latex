{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    typix = {
      url = "github:loqusion/typix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    myPackages = {
      url = "github:billy4479/nix-packages";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
      };
    };
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      typix,
      myPackages,
      ...
    }:
    let
      documents = [
        "game-theory"
        "finance"
        "stochastic-processes"

        "gt-ps1"
        "gt-ps2"
        "gt-ps3"
        "gt-ps4"

        "finance-chsh"

        "information-theory-evolutionary-models"
        "neuroscience"
      ];

    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        myPkgs = myPackages.packages.${system};
        fonts = with pkgs; [
          nerd-fonts.fira-code
          ubuntu-sans
          excalifont # excalidraw font
          noto-fonts-color-emoji

          myPkgs.google-sans
        ];

        typixLib = typix.lib.${system};
        typixCommonArgs = {
          src = typixLib.cleanTypstSource ./.;

          fontPaths = map (pkg: "${pkg}/share/fonts/truetype") fonts;
          emojiFont = "noto";

          virtualPaths = [
            {
              dest = "assets";
              src = ./assets;
            }
          ];

          unstable_typstPackages = [
            {
              name = "headcount";
              version = "0.1.0";
              hash = "sha256-60Mf/TKEOgsd+kpvV151L4Au1E4tO0FMgQLu3JY18BA=";
            }
            {
              name = "great-theorems";
              version = "0.1.2";
              hash = "sha256-AsEQ4VpiYaOchBgQSnv5DayAOwCtAZp2UWzkjwN6AvU=";
            }
            {
              name = "equate";
              version = "0.3.2";
              hash = "sha256-i9FRB+byS9atlU0DvMWmNxIVEEYO85/4wEDJaitWSVA=";
            }
            {
              name = "hydra";
              version = "0.6.2";
              hash = "sha256-soNQLPonThDhunHQEfpiXJ/cpRGzz48D4E0Nmg3w/Js=";
            }
            {
              name = "physica";
              version = "0.9.7";
              hash = "sha256-G2M428hUZ8g7IwDjK9gRji9owpTiqn5I+QYMS4XcyfA=";
            }
            # dependency of hydra
            {
              name = "oxifmt";
              version = "1.0.0";
              hash = "sha256-edTDK5F2xFYWypGpR0dWxwM7IiBd8hKGQ0KArkbpHvI=";
            }
          ];
        };

        typixDerivations = map (
          name:
          let
            args = typixCommonArgs // {
              typstSource = "${name}.typ";
              typstOutput = "build/${name}.pdf";
            };
          in
          {
            inherit name;
            buildDrv = typixLib.buildTypstProject args;
            buildScript = typixLib.buildTypstProjectLocal args // {
              scriptName = "typst-build-${name}";
            };
            watchScript =
              typixLib.watchTypstProject (
                builtins.removeAttrs args [
                  "src"
                  "unstable_typstPackages"
                ]
              )
              // {
                scriptName = "typst-watch-${name}";
              };
          }
        ) documents;
      in
      {
        devShells.default = typixLib.devShell {
          packages =
            with pkgs;
            [
              mupdf-headless
              pandoc
              nodePackages_latest.svgo

              typstyle
              tinymist

              nixd
            ]
            ++ map (x: x.watchScript) typixDerivations;
        };

        apps = builtins.foldl' (
          a: x:
          a
          // {
            "build-${x.name}" = flake-utils.lib.mkApp {
              drv = x.buildScript;
            };
            "watch-${x.name}" = flake-utils.lib.mkApp {
              drv = x.watchScript;
            };
          }
        ) { } typixDerivations;

        packages = builtins.foldl' (a: x: a // { "${x.name}" = x.buildDrv; }) rec {
          all-typst = pkgs.linkFarm "typst-documents" (
            map (x: {
              name = "${x.name}.pdf";
              path = x.buildDrv;
            }) typixDerivations
          );

          default = all-typst;
        } typixDerivations;
      }
    );
}
