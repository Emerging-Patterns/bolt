{
  description = "bolt: a linter, checker and language server for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.34 (the v2.0.34 tag
  # still packages 2.0.33): bolt builds on it, lints itself with the bolt it
  # builds, and checks.proofs runs every PROOF.bend on it
  inputs.bend = {
    url = "github:bendlang/bend/777ee0b55c485afdd7e68bd917b3d23a88d77371";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    # ez's flake.lock names the same 2.0.34 commit as inputs.bend
    inputs.bend.follows = "bend";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      ez = inputs.ez.lib.${system};
      bend = inputs.bend.packages.${system}.default;
      bend-cc = ez.bend-cc;
      rawRev = self.shortRev or (self.dirtyShortRev or "");
      shortRev = builtins.substring 0 7 rawRev;
      bakedRev =
        if builtins.match "[0-9a-f]{7}" shortRev == null then "" else shortRev;
      boltPkg = ez.mkPackage {
        inherit bend;
        src = self;
        version = "1.13.0"; # x-release-please-version
        wrapFlags = [ "--gpu" "off" ];
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
      # the proof gate: `ez prove`, every PROOF.bend on this flake's bend,
      # each passing only on a first line of ALL PROOFS CHECK
      proofs = ez.mkProofs { ez = inputs.ez.packages.${system}.default; src = self; };
      # bolt, built from this tree, over this tree: exit 1 on any error
      lint = ez.mkLint { inherit bolt; src = self; };
    in {
      packages.${system} = { inherit bolt bend bend-cc; default = bolt; };
      checks.${system} = { inherit bolt proofs lint; };
      apps.${system}.default = { type = "app"; program = "${bolt}/bin/bolt"; };
      devShells.${system}.default = ez.mkShell {
        packages = [ bend bend-cc pkgs.nodejs pkgs.git ];
      };
    };
}
