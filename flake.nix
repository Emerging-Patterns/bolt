{
  description = "bolt: a linter, checker and language server for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.bend = {
    url = "github:bendlang/bend";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.follows = "bend";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      ez = inputs.ez.lib.${system};
      ezBin = inputs.ez.packages.${system}.default;
      bend = inputs.bend.packages.${system}.default;
      bend-cc = ez.bend-cc;
      # ez.bendLib checks sha256sum. This lock's digests are ez's, so the
      # package and checks.test take BEND_LIB from nix/bend-lib.nix.
      bendLib = pkgs.callPackage ./nix/bend-lib.nix { } ./ez.lock.toml;
      bolt = (ez.mkPackage {
        inherit bend;
        src = self;
        version = "0.4.0";  # keep with editors/vscode/package.json and bolt/version.bend
        wrapFlags = [ "--gpu" "off" ];
        meta = {
          description = "A linter, checker and language server for Bend 2";
          license = pkgs.lib.licenses.mit;
        };
      }).overrideAttrs (_old: {
        BEND_LIB = bendLib;
      });
      # proofs and unit tests (`ez test --unit-only`).
      test = (ez.mkProofs {
        ez = ezBin;
        src = self;
        name = "bolt-test";
        extraFlags = [ "--unit-only" ];
      }).overrideAttrs (_old: {
        BEND_LIB = bendLib;
      });
    in {
      packages.${system} = { inherit bolt bend bend-cc; default = bolt; };
      checks.${system} = { inherit bolt test; };
      apps.${system}.default = { type = "app"; program = "${bolt}/bin/bolt"; };
      devShells.${system}.default = ez.mkShell {
        packages = [ bend bend-cc pkgs.nodejs pkgs.git ];
      };
    };
}
