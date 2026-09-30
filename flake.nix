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
    # ez stays on the bend its own flake.lock records (2.0.31) until ez
    # releases on 2.0.34, so ez's inputs.bend is pinned, not followed
    inputs.bend.url = "github:bendlang/bend/af569d4826913b2ce3557e9829ccad31fcf86f94";
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
        version = "1.10.0"; # x-release-please-version
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
      # the proof gate: every PROOF.bend on this flake's bend, its first line
      # ALL PROOFS CHECK. ez.mkProofs comes back when ez runs on 2.0.34.
      proofs = pkgs.runCommand "bolt-proofs" {
        nativeBuildInputs = [ bend ];
        BEND_LIB = ez.bendLib ./ez.lock.toml;
      } ''
        export HOME=$TMPDIR
        cp -r ${self} src && chmod -R u+w src && cd src
        for p in $(find . -name PROOF.bend -not -path './.ez/*' | sort); do
          first=$(cd "$(dirname "$p")" && bend "$(basename "$p")" | head -n 1)
          echo "$p: $first"
          [ "$first" = "ALL PROOFS CHECK" ] || exit 1
        done
        touch $out
      '';
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
