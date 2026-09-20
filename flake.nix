{
  # the flake carries the C toolchain bolt builds with; bend itself comes
  # from bendlang/bend's own flake (the release archive, patched for nix)
  description = "bolt: a linter, checker and language server for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.bend = {
    url = "github:bendlang/bend";
    inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      llvm = pkgs.llvmPackages_19;
      # bend needs clang 19+ for a GPU build. The wrapped nix clang links nix's
      # glibc, and then nvrtc cannot load the system libstdc++; so: the
      # unwrapped clang, its resource dir, the system's dynamic linker and the
      # system's ld (bend's wrapper puts nix's clang on PATH, whose wrapped ld
      # would add a runpath to nix's glibc; CC=bend-cc still wins for a GPU build).
      # The gate runs the CPU lane only; a GPU build is `bend x.bend -o x` in
      # the dev shell, run with `--gpu 1GB`.
      bend-cc = pkgs.writeShellScriptBin "bend-cc" ''
        exec ${llvm.clang-unwrapped}/bin/clang \
          -resource-dir ${llvm.clang}/resource-root \
          --ld-path=/usr/bin/ld \
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
      # bend 2 itself, from its own flake: the wrapper puts nix's clang on
      # PATH for `bend -o`, and bend-cc on CC still wins for a GPU build
      bend = inputs.bend.packages.${system}.default;
      # bolt: bend emits the C, clang 19 builds it; the wrapper puts bend on
      # its PATH (for `bolt check` and the server's diagnostics) and keeps it
      # off the GPU, which is slower for this work (bolt/lsp/bench)
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
          cp bolt.bin $out/bin/bolt
          wrapProgram $out/bin/bolt --prefix PATH : ${pkgs.lib.makeBinPath [ bend ]} \
            --add-flags "--gpu off"
        '';
        meta = {
          description = "A linter, checker and language server for Bend 2";
          license = pkgs.lib.licenses.mit;
          mainProgram = "bolt";
        };
      };
    in {
      packages.${system} = { inherit bend bolt bend-cc; default = bolt; };
      apps.${system}.default = { type = "app"; program = "${bolt}/bin/bolt"; };
      checks.${system} = { c = c-check; inherit bolt; };
      devShells.${system}.default = pkgs.mkShellNoCC {
        packages = [ bend bend-cc ];
        shellHook = "export CC=bend-cc";
      };
    };
}
