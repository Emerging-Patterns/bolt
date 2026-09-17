{
  description = "bend monorepo: the toolchain for native and GPU builds";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      llvm = pkgs.llvmPackages_19;
      # bend needs clang 19+ for a GPU build. The wrapped nix clang links nix's
      # glibc, and then nvrtc cannot load the system libstdc++; so: the
      # unwrapped clang, its resource dir, and the system's dynamic linker.
      bend-cc = pkgs.writeShellScriptBin "bend-cc" ''
        exec ${llvm.clang-unwrapped}/bin/clang \
          -resource-dir ${llvm.clang}/resource-root \
          -Wl,--dynamic-linker=/lib64/ld-linux-x86-64.so.2 "$@"
      '';
    in {
      packages.${system}.bend-cc = bend-cc;
      devShells.${system}.default = pkgs.mkShellNoCC {
        packages = [ bend-cc ];
        shellHook = "export CC=bend-cc";
      };
    };
}
