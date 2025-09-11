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
        "stochastics-processes"
      ];

    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        myPkgs = myPackages.packages.${system};
        fonts = with pkgs; [
          nerd-fonts.fira-code
          ubuntu_font_family
          fg-virgil # excalidraw font
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
      rec {
        devShells.default = typixLib.devShell {
          packages =
            with pkgs;
            [
              mupdf-headless

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

        packages = builtins.foldl' (a: x: a // { "${x.name}" = x.buildDrv; }) (rec {
          all-typst = pkgs.linkFarm "typst-documents" (
            map (x: {
              name = "${x.name}.pdf";
              path = x.buildDrv;
            }) typixDerivations
          );

          default = all-typst;
        }) typixDerivations;
      }
    );
}
