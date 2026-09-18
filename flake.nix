{
  description = "bolt: the C toolchain for native builds (and, by hand, GPU ones)";

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
    in {
      packages.${system}.bend-cc = bend-cc;
      checks.${system}.c = c-check;
      devShells.${system}.default = pkgs.mkShellNoCC {
        packages = [ bend-cc ];
        shellHook = "export CC=bend-cc";
      };
    };
}
