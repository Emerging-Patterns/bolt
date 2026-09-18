{
  # the flake carries the C toolchain bolt builds with; bend itself is not
  # packaged in nix (`bend` installs from bend-lang.com)
  description = "bolt: a linter, checker and language server for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      llvm = pkgs.llvmPackages_19;
      # bend needs clang 19+ for a GPU build. The wrapped nix clang links nix's
      # glibc, and then nvrtc cannot load the system libstdc++; so: the
      # unwrapped clang, its resource dir, and the system's dynamic linker.
      # The gate runs the CPU lane only; a GPU build is `bend x.bend -o x` in
      # the dev shell, run with `--gpu 1GB`.
      bend-cc = pkgs.writeShellScriptBin "bend-cc" ''
        exec ${llvm.clang-unwrapped}/bin/clang \
          -resource-dir ${llvm.clang}/resource-root \
          -Wl,--dynamic-linker=/lib64/ld-linux-x86-64.so.2 "$@"
      '';
      # what bend's generated C needs of a toolchain: C11 with atomics,
      # pthreads, libm, mmap; built and run, in the sandbox, with the same
      # clang 19 (nix's wrapper stands in for the system libc there)
      c-check = pkgs.runCommand "bolt-c-check" { nativeBuildInputs = [ llvm.clang ]; } ''
        cat > t.c <<'EOF'
        #include <math.h>
        #include <pthread.h>
        #include <stdatomic.h>
        #include <stdint.h>
        #include <stdio.h>
        #include <sys/mman.h>
        static atomic_uint_fast64_t n;
        static void *work(void *_) { for (int i = 0; i < 1000; i++) atomic_fetch_add(&n, 1); return 0; }
        int main(void) {
          pthread_t t[4];
          for (int i = 0; i < 4; i++) pthread_create(&t[i], 0, work, 0);
          for (int i = 0; i < 4; i++) pthread_join(t[i], 0);
          void *m = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
          printf("%lu %.0f %d\n", (unsigned long)atomic_load(&n), sqrt(16.0), m != MAP_FAILED);
          return 0;
        }
        EOF
        clang -std=c11 -O3 t.c -lpthread -lm -o t
        got=$(./t)
        [ "$got" = "4000 4 1" ] || { echo "got: $got"; exit 1; }
        echo "$got" > $out
      '';
      # bend 2 itself: a release tarball of TypeScript that bun runs, with no
      # dependencies of its own. The launcher from bend-lang.com is replaced by
      # a plain one: no telemetry, no self-update, this version only.
      bend = pkgs.stdenvNoCC.mkDerivation rec {
        pname = "bend";
        version = "2.0.3";
        src = pkgs.fetchurl {
          url = "https://bend-lang.com/dl/${version}.tar.gz";
          sha256 = "f967e73ca5481bd49940dcd966705082a43c209ac1bdb390b849c8652fff5a17";
        };
        sourceRoot = ".";
        installPhase = ''
          mkdir -p $out/share/bend $out/bin
          cp -r bend2 guide $out/share/bend/
          cat > $out/bin/bend <<EOF
          #!${pkgs.runtimeShell}
          exec ${pkgs.bun}/bin/bun $out/share/bend/bend2/main.ts "\$@"
          EOF
          chmod +x $out/bin/bend
        '';
      };
      # bolt: bend emits the C, clang 19 builds it; the `bolt` script sits
      # beside the binary and finds bend on its PATH (for `bolt check` and
      # the server's diagnostics)
      bolt = pkgs.stdenv.mkDerivation {
        pname = "bolt";
        version = "0.3.0";  # keep with editors/vscode/package.json
        src = self;
        nativeBuildInputs = [ bend llvm.clang pkgs.makeWrapper ];
        buildPhase = ''
          bend bolt/main.bend -o bolt.c
          clang -std=c11 -O3 bolt.c -lpthread -lm -o bolt.bin
        '';
        installPhase = ''
          mkdir -p $out/bin
          cp bolt.bin $out/bin/bolt.bin
          cp bolt/bolt $out/bin/bolt
          wrapProgram $out/bin/bolt --prefix PATH : ${pkgs.lib.makeBinPath [ bend pkgs.findutils pkgs.coreutils ]}
        '';
      };
    in {
      packages.${system} = { inherit bend bolt bend-cc; default = bolt; };
      apps.${system}.default = { type = "app"; program = "${bolt}/bin/bolt"; };
      checks.${system} = { c = c-check; inherit bolt; };
      devShells.${system}.default = pkgs.mkShellNoCC {
        packages = [ bend-cc ];
        shellHook = "export CC=bend-cc";
      };
    };
}
