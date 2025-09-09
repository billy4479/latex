{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    typix = {
      url = "github:loqusion/typix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      typix,
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
        fonts = with pkgs; [
          nerd-fonts.fira-code
          ubuntu_font_family
          fg-virgil # excalidraw font
          noto-fonts-color-emoji
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
              name = "cetz";
              version = "0.4.2";
              hash = "sha256-qBIEHqtiMSG/WoXHPC/rQ9VkestSvVNlUwTmAMX1wAs=";
            }
            # Required by cetz
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
