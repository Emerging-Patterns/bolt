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
      # shake v0.1.1, the git-backed ledger dep bolt's CLI imports. The nix
      # sandbox cannot fetch 0x imports, so the same rev and narHash as
      # ez.toml are fetched here and offered as BEND_LIB.
      shakeSrc = pkgs.fetchgit {
        url = "https://github.com/Emerging-Patterns/shake";
        rev = "cb02b47e80fdab81dbaa8c3cec2356f7a22d02b0";
        hash = "sha256-G4uW2UV4Me6lJYxGU5rfn2kvJKs+/un4Hc0OjcirL7A=";
      };
      shakeLib = pkgs.runCommand "bolt-shake-lib" { inherit shakeSrc; } ''
        mkdir -p $out/0x65bf91e14c96bf0c25491d716ec9f68c
        cp $shakeSrc/shake/main.bend $out/0x65bf91e14c96bf0c25491d716ec9f68c/main.bend
      '';
      # bolt, built the one way anything builds it: `bend <entry> -o <binary>`.
      # That is not a shorter spelling of emitting the C and compiling it by
      # hand -- it is the same compile. bend runs the C it emits through
      # `-std=c11 -O3 <file> -lpthread -lm -o <bin>`, which is flag for flag
      # what the two-step form here used to spell out, so the two-step form
      # bought nothing and only let this build drift from every other one.
      # It does hand the choice of clang to bend, which takes $CC first and
      # then the newest `clang-<n>` on the PATH -- here clang 21, from bend's
      # own wrapper, where the two-step form named clang 19. Measured over
      # this repo, seven runs each, that is 1.69 s against 1.73 s at the
      # median: no difference worth a line of nix.
      # The wrapper puts bend on the binary's PATH (for `bolt check` and the
      # server's diagnostics) and keeps it off the GPU, which is slower for
      # this work (bolt/lsp/bench).
      bolt = pkgs.stdenv.mkDerivation {
        pname = "bolt";
        version = "0.4.0";  # keep with editors/vscode/package.json
        src = self;
        nativeBuildInputs = [ bend pkgs.makeWrapper ];
        BEND_LIB = shakeLib;
        buildPhase = ''
          bend bolt/main.bend -o bolt.bin
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
      # the shell the gate runs in. node is here because two of the end-to-end
      # tests drive one -- the server spawned over sockets, and the extension's
      # binary resolution -- and a gate that borrowed whatever node the machine
      # happened to have would answer a different question on every machine.
      # bolt itself needs none of this: `bend bolt/main.bend -o bin/bolt.bin`
      # is the whole build once shake is on BEND_LIB (tests/bare.bend).
      # The package build above takes shake from the store. The shell does
      # not: `ez fetch` writes the lock into `.ez/lib`, and a store path is
      # read-only (CI failed that way). Same as ez's own default shell.
      devShells.${system}.default = pkgs.mkShellNoCC {
        packages = [ bend bend-cc pkgs.nodejs pkgs.git ];
        shellHook = ''
          export CC=bend-cc
          export BEND_LIB=$PWD/.ez/lib
        '';
      };
    };
}
