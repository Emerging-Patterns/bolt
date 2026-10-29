{
  description = "bolt: a linter, checker and language server for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.38 (the v2.0.38 tag
  # may still package 2.0.37): bolt and ez build on it, bolt lints itself with
  # the bolt it builds, and checks.proofs runs every PROOF.bend on it
  inputs.bend = {
    url = "github:bendlang/bend/042e797ebd1cfc060603e2682879909fe86fa8c2";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.follows = "bend";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
      forEach = nixpkgs.lib.genAttrs systems;
      outputsFor = system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          ez = inputs.ez.lib.${system};
          ezBin = inputs.ez.packages.${system}.default;
          bend = inputs.bend.packages.${system}.default;
          bend-cc = ez.bend-cc;
          rawRev = self.shortRev or (self.dirtyShortRev or "");
          shortRev = builtins.substring 0 7 rawRev;
          bakedRev =
            if builtins.match "[0-9a-f]{7}" shortRev == null then "" else shortRev;
          boltPkg = ez.mkPackage {
            inherit bend;
            src = self;
            version = "1.20.0"; # x-release-please-version
            # the runtime's options go between +RTS and -RTS (bend 2.0.38)
            wrapFlags = [ "+RTS" "--gpu" "off" "-RTS" ];
            meta = {
              description = "A linter, checker and language server for Bend 2";
              license = pkgs.lib.licenses.mit;
            };
          };
          # short commit id, written into src/build_rev.bend before bend runs
          bolt = if bakedRev == "" then boltPkg else boltPkg.overrideAttrs (old: {
            buildPhase = ''
              chmod u+w src/build_rev.bend
              printf '%s\n%s\n\n%s\n%s\n%s\n' \
                '# the short commit id of this build. Empty when the build has none.' \
                'import Base' \
                '# the short commit id, or empty' \
                'def text() -> String:' \
                '  "${bakedRev}"' \
                > src/build_rev.bend
              ${old.buildPhase}
            '';
          });
          # the proof gate: every PROOF.bend on this flake's bend, each passing
          # only on a first line of ALL PROOFS CHECK
          proofs = ez.mkProofs { ez = ezBin; src = self; };
          # bolt, built from this tree, over this tree: exit 1 on any error
          lint = ez.mkLint { inherit bolt; src = self; };
        in {
          packages = {
            inherit bolt bend bend-cc;
            ez = ezBin;
            default = bolt;
          };
          checks = { inherit bolt proofs lint; };
          apps.default = { type = "app"; program = "${bolt}/bin/bolt"; };
          devShells.default = ez.mkShell {
            packages = [ bend bend-cc pkgs.nodejs pkgs.git ];
          };
        };
      perSystem = forEach outputsFor;
      each = name: forEach (system: perSystem.${system}.${name});
    in {
      packages = each "packages";
      checks = each "checks";
      apps = each "apps";
      devShells = each "devShells";
    };
}
