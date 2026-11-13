#!/usr/bin/env python3
"""Mutation sweep over bolt's src/: which defs can change without a proof failing.

Run inside `nix develop` from the repo root:  python3 sweep.py <repo> <scratch> [workers] [per_def]
Each mutant is one line changed in one def, by an operator that keeps types:
  flip   True{} <-> False{}            (never on a `case` line)
  andor  Bool.and( <-> Bool.or(
  unnot  Bool.not(  -> Bool.and(True{},
  drop   `x <> f(..)` as a whole arm   -> `f(..)`
A mutant SURVIVES when `bend PROOF.bend --check-only` still prints ALL PROOFS CHECK.
A file is LOADED when breaking it makes the check fail (else no proof imports it).
"""
import os, re, shutil, subprocess, sys, json
from concurrent.futures import ThreadPoolExecutor
from queue import Queue

repo, scratch = sys.argv[1], sys.argv[2]
workers = int(sys.argv[3]) if len(sys.argv) > 3 else 16
per_def = int(sys.argv[4]) if len(sys.argv) > 4 else 3

def src_files():
    out = []
    for d, _, fs in os.walk(os.path.join(repo, "src")):
        if any(p in d for p in ("/tests", "/fixtures", "/bench")):
            continue
        for f in fs:
            if f.endswith(".bend"):
                out.append(os.path.relpath(os.path.join(d, f), repo))
    return sorted(out)

DROP = re.compile(r"^(\s+)(\S.*?) <> ([A-Za-z_][\w.]*\(.*\))$")

def ops(line):
    s = line.rstrip("\n")
    st = s.strip()
    if not st or st.startswith("#") or st.startswith("case ") or st.startswith("match "):
        return []
    code = s.split("  #")[0]
    out = []
    if "True{}" in code:
        out.append(("flip", s.replace("True{}", "False{}", 1)))
    elif "False{}" in code:
        out.append(("flip", s.replace("False{}", "True{}", 1)))
    if "Bool.and(" in code:
        out.append(("andor", s.replace("Bool.and(", "Bool.or(", 1)))
    elif "Bool.or(" in code:
        out.append(("andor", s.replace("Bool.or(", "Bool.and(", 1)))
    if "Bool.not(" in code:
        out.append(("unnot", s.replace("Bool.not(", "Bool.and(True{}, ", 1)))
    m = DROP.match(s)
    if m and s.count("(") == s.count(")") and "=" not in m.group(2).split("(")[0]:
        out.append(("drop", m.group(1) + m.group(3)))
    return out

def mutants():
    ms, probed, unprobed = [], 0, []
    for f in src_files():
        lines = open(os.path.join(repo, f)).read().split("\n")
        i = 0
        while i < len(lines):
            if lines[i].startswith("def "):
                name = lines[i][4:].split("(")[0].strip()
                skip = "noqa: L001" in lines[i]
                j = i + 1
                while j < len(lines) and (lines[j].startswith(" ") or lines[j] == "" or lines[j].startswith(")")):
                    j += 1
                # the body starts after the signature's closing `:` line
                k = i
                while k < j and not lines[k].rstrip().endswith(":"):
                    k += 1
                cands = []
                for n in range(k + 1, j):
                    for op, new in ops(lines[n]):
                        cands.append((n, op, new))
                if skip:
                    pass
                elif cands:
                    probed += 1
                    # spread: prefer distinct operators, then distinct lines
                    seen_ops, picked = set(), []
                    for c in cands:
                        if c[1] not in seen_ops:
                            picked.append(c); seen_ops.add(c[1])
                    for c in cands:
                        if len(picked) >= per_def:
                            break
                        if c not in picked:
                            picked.append(c)
                    for n, op, new in picked[:per_def]:
                        ms.append({"file": f, "def": name, "line": n + 1, "op": op, "new": new, "old": lines[n]})
                else:
                    unprobed.append((f, name))
                i = j
            else:
                i += 1
    return ms, probed, unprobed

def setup(n):
    dirs = []
    for w in range(n):
        d = os.path.join(scratch, "w%02d" % w)
        if os.path.exists(d):
            shutil.rmtree(d)
        os.makedirs(d)
        for item in ("src", "laws", "proofs", "LAWS.bend", "PROOF.bend", "main.bend", "bolt.bend", "ez.toml",
                     "ez.lock.toml", "json", "core", "lazy", "syntax"):
            p = os.path.join(repo, item)
            if os.path.isdir(p):
                shutil.copytree(p, os.path.join(d, item), symlinks=True)
            elif os.path.exists(p):
                shutil.copy(p, os.path.join(d, item))
        dirs.append(d)
    return dirs

def check(d):
    try:
        r = subprocess.run(["bend", "PROOF.bend", "--check-only"], cwd=d, capture_output=True, text=True, timeout=180)
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return "timeout"
    if "ALL PROOFS CHECK" in out:
        return "survived"
    return "killed"

def main():
    ms, probed, unprobed = mutants()
    files = src_files()
    print("files", len(files), "defs probed", probed, "defs with no operator", len(unprobed), "mutants", len(ms), flush=True)
    dirs = setup(workers)
    base = check(dirs[0])
    print("baseline:", base, flush=True)
    assert base == "survived"
    pool = Queue()
    for d in dirs:
        pool.put(d)

    def run_file(f):
        d = pool.get()
        try:
            p = os.path.join(d, f)
            orig = open(p).read()
            open(p, "w").write(orig + '\ndef zz.broken() -> U32:\n  "not a number"\n')
            r = check(d)
            open(p, "w").write(orig)
            return f, r
        finally:
            pool.put(d)

    def run_mut(m):
        d = pool.get()
        try:
            p = os.path.join(d, m["file"])
            orig = open(p).read()
            lines = orig.split("\n")
            assert lines[m["line"] - 1] == m["old"]
            lines[m["line"] - 1] = m["new"]
            open(p, "w").write("\n".join(lines))
            r = check(d)
            open(p, "w").write(orig)
            return dict(m, status=r)
        finally:
            pool.put(d)

    with ThreadPoolExecutor(workers) as ex:
        loaded = dict(ex.map(run_file, files))
        json.dump(loaded, open(os.path.join(scratch, "loaded.json"), "w"), indent=1)
        print("files not loaded by any proof:", sorted(f for f, r in loaded.items() if r == "survived"), flush=True)
        todo = [m for m in ms if loaded[m["file"]] != "survived"]
        print("mutants in loaded files:", len(todo), flush=True)
        res, done = [], 0
        for r in ex.map(run_mut, todo):
            res.append(r); done += 1
            if done % 200 == 0:
                print(done, "done,", sum(1 for x in res if x["status"] == "survived"), "survived", flush=True)
    json.dump({"results": res, "unprobed": unprobed, "loaded": loaded}, open(os.path.join(scratch, "sweep.json"), "w"), indent=1)
    surv = [r for r in res if r["status"] == "survived"]
    print("survived", len(surv), "of", len(res), "; timeouts", sum(1 for r in res if r["status"] == "timeout"))

main()
