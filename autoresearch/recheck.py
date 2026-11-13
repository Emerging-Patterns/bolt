"""Re-run a sweep's survivors against a repo: python3 recheck.py <sweep.json> <repo> <scratch> [workers] -> <scratch>/recheck.json"""
import json, os, sys, shutil, subprocess
from concurrent.futures import ThreadPoolExecutor
from queue import Queue
sw, repo, scratch = sys.argv[1], sys.argv[2], sys.argv[3]
workers = int(sys.argv[4]) if len(sys.argv) > 4 else 16
surv = [r for r in json.load(open(sw))["results"] if r["status"] == "survived"]
dirs = []
for w in range(workers):
    d = os.path.join(scratch, "w%02d" % w)
    if os.path.exists(d): shutil.rmtree(d)
    os.makedirs(d)
    for item in ("src", "laws", "proofs", "LAWS.bend", "PROOF.bend", "main.bend", "bolt.bend", "ez.toml", "ez.lock.toml"):
        p = os.path.join(repo, item)
        if os.path.isdir(p): shutil.copytree(p, os.path.join(d, item), symlinks=True)
        elif os.path.exists(p): shutil.copy(p, os.path.join(d, item))
    dirs.append(d)
pool = Queue()
for d in dirs: pool.put(d)
def run(m):
    d = pool.get()
    try:
        p = os.path.join(d, m["file"]); orig = open(p).read(); lines = orig.split("\n")
        if lines[m["line"] - 1] != m["old"]:
            return dict(m, status="moved")
        lines[m["line"] - 1] = m["new"]; open(p, "w").write("\n".join(lines))
        r = subprocess.run(["bend", "PROOF.bend", "--check-only"], cwd=d, capture_output=True, text=True, timeout=180)
        open(p, "w").write(orig)
        return dict(m, status="survived" if "ALL PROOFS CHECK" in r.stdout + r.stderr else "killed")
    finally:
        pool.put(d)
with ThreadPoolExecutor(workers) as ex:
    res = list(ex.map(run, surv))
json.dump(res, open(os.path.join(scratch, "recheck.json"), "w"), indent=1)
k = [r for r in res if r["status"] == "killed"]
print("killed", len(k), "of", len(res), "; moved", sum(r["status"] == "moved" for r in res))
for r in k: print(" ", r["op"], r["file"] + ":" + str(r["line"]), r["def"])
