# BEND_LIB from ez.lock.toml. ez.bendLib checks sha256sum of the raw
# bytes; the lock records ez's digest, the low 8 bits of each codepoint.
# Those differ when a file is not ASCII (snap par.c, shake main.bend).
{ lib, fetchgit, runCommand, python3, writeText }:

lockFile:

let
  doc = builtins.fromTOML (builtins.readFile lockFile);

  manifest = files:
    lib.concatStrings (map (p: "${files.${p}} ${p}\n") (lib.naturalSort (builtins.attrNames files)));

  gitSrc = hash: source: fetchgit {
    inherit (source) url rev;
    name = "bend-${lib.removePrefix "0x" hash}-src";
    hash = source.narHash;
  };

  sum = writeText "bend-sum.py" ''
    import hashlib, pathlib, sys
    path, want = sys.argv[1], sys.argv[2]
    text = pathlib.Path(path).read_bytes().decode("utf-8")
    got = hashlib.sha256(bytes(ord(c) & 255 for c in text)).hexdigest()
    if got != want:
        raise SystemExit(f"{path}: {got}, want {want}")
  '';

  pkg = hash: entry:
    if entry.source.kind != "git" then
      throw "nix/bend-lib.nix: ${hash} is ${entry.source.kind}"
    else ''
      mkdir -p "$out/${hash}"
      from=${gitSrc hash entry.source}/${entry.source.root}
      ${lib.concatStrings (lib.mapAttrsToList (at: sha256: ''
        mkdir -p "$out/${hash}/$(dirname ${lib.escapeShellArg at})"
        cp "$from/${at}" "$out/${hash}/${at}"
        python3 ${sum} "$out/${hash}/${at}" ${lib.escapeShellArg sha256}
      '') entry.files)}
      printf '%s' ${lib.escapeShellArg (manifest entry.files)} > "$out/${hash}/manifest"
    '';
in
runCommand "bend-lib" { nativeBuildInputs = [ python3 ]; }
  (lib.concatStrings ([ "mkdir -p $out\n" ] ++ lib.mapAttrsToList pkg doc.packages))
