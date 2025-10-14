{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        agdaDependencies = [
          pkgs.agdaPackages.agda-categories
          pkgs.agdaPackages.standard-library
        ];
        agda-html = pkgs.agdaPackages.mkDerivation {
          pname = "dinaturality";
          version = "0.1.0";
          src = builtins.path { path = ./.; name = "dinaturality"; };
          everythingFile = ./All.agda;
          buildInputs = agdaDependencies;

          installPhase = '''';

          buildPhase = ''
            runHook preBuild
            # Make sure this builds with --safe
            agda --html --html-dir=$out --highlight-occurrences --safe All.agda +RTS -M32G
            runHook postBuild
          '';

          preConfigure = ''export AGDA_EXEC=agda'';
          LC_ALL = "en_US.UTF-8";
          nativeBuildInputs = [ pkgs.glibcLocales ];

          meta = {
            platforms = pkgs.lib.platforms.unix;
          };
        }; in {
        devShells.default = pkgs.mkShell { buildInputs = [
          (pkgs.agda.withPackages agdaDependencies)
        ]; };
        packages = {
          inherit agda-html;
          default = agda-html;
        };
      }
    );
}
