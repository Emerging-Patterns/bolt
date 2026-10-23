{
  description = "bolt: a linter, checker and language server for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.38 (the v2.0.38 tag
  # may still package 2.0.37): bolt builds on it, lints itself with the bolt it
  # builds, and checks.proofs runs every PROOF.bend on it
  inputs.bend = {
    url = "github:bendlang/bend/042e797ebd1cfc060603e2682879909fe86fa8c2";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  # ez stays on the bend its own flake.lock records (2.0.36) until it releases
  # on 2.0.38: it does not check on 2.0.38 yet. The tooling pass puts
  # `inputs.bend.follows = "bend"` and ez.mkProofs back then.
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.url = "github:bendlang/bend/eebc18cd04daeade06c3f68c3c96c1faefd3462f";
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
        version = "1.17.0"; # x-release-please-version
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
      # only on a first line of ALL PROOFS CHECK. A shell loop until ez
      # releases on 2.0.38 and ez.mkProofs runs on it (the tooling pass).
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
      packages.${system} = {
        inherit bolt bend bend-cc;
        ez = inputs.ez.packages.${system}.default;
        default = bolt;
      };
      checks.${system} = { inherit bolt proofs lint; };
      apps.${system}.default = { type = "app"; program = "${bolt}/bin/bolt"; };
      devShells.${system}.default = ez.mkShell {
        packages = [ bend bend-cc pkgs.nodejs pkgs.git ];
      };
    };
}
