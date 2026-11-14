{
  description = "bolt: a linter, checker and language server for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.40 (the v2.0.40 tag
  # may still package 2.0.39): bolt and ez build on it, bolt lints itself with
  # the bolt it builds, and checks.proofs runs every PROOF.bend on it
  inputs.bend = {
    url = "github:bendlang/bend/222de9901d4e3551c2b347da02e02a10098a28b2";
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
            version = "1.53.0"; # x-release-please-version
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
          # the packaged bolt as an editor starts it: spawned by node over
          # sockets (src/lsp/tests/spawn.js), found and started the way the
          # extension finds it (tests/locate.js), and the server over the
          # real checker (src/lsp/tests/checker.bend). A server that builds
          # and proves can still never answer: bolt's did not, from the bend
          # 2.0.40 pin until this check existed
          # src/lsp/tests/checker.bend as a binary: interpreted, it overflows
          # the stack reading this tree's larger proofs, so it runs native
          checkerTest = ez.mkPackage {
            inherit bend;
            src = self;
            pname = "bolt-checker-test";
            version = "0";
            entry = "src/lsp/tests/checker.bend";
            wrapFlags = [ "+RTS" "--gpu" "off" "-RTS" ];
          };
          lsp = pkgs.runCommand "bolt-lsp" { nativeBuildInputs = [ pkgs.nodejs ]; } ''
            cp -r ${self} tree
            chmod -R u+w tree
            cd tree
            export HOME=$TMPDIR
            # tests/locate.js also looks for the checkout's own build
            mkdir -p bin
            ln -s ${bolt}/bin/bolt bin/bolt.bin
            node src/lsp/tests/spawn.js bin/bolt.bin
            node tests/locate.js bin/bolt.bin
            # the server over the real checker, against the lines the test
            # file ends in
            grep '^#|' src/lsp/tests/checker.bend | sed 's/^#|//' > want.txt
            ${checkerTest}/bin/bolt-checker-test > got.txt
            diff want.txt got.txt
            touch $out
          '';
        in {
          packages = {
            inherit bolt bend bend-cc;
            ez = ezBin;
            default = bolt;
          };
          checks = { inherit bolt proofs lint lsp; };
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
