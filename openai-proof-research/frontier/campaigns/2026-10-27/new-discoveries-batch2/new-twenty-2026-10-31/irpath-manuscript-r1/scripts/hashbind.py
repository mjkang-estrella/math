"""Hash-bind the frozen read-only inputs of lane irpath-manuscript-r1.

Usage (run from the lane directory):
  python3 -I scripts/hashbind.py snapshot OUT.json      write a new snapshot (mode 'x': never overwrites)
  python3 -I scripts/hashbind.py compare BEFORE AFTER OUT.json

Inputs are files and directories of the campaign directory (the lane's parent). Symlinks are
recorded, never followed. Only reads inside the inputs; writes only OUT.
"""
import sys
sys.dont_write_bytecode = True
import hashlib, json, os, datetime

CAMPAIGN = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CAMPAIGN = os.path.dirname(CAMPAIGN)
INPUTS = [
    "expanded-corpus-r209",
    "irpath-review-r1",
    "irpath-root-check-r1",
    "irpath-root-ruling-r1.json",
    "irpath-formal-r1",
    "irpath-parent-final-r1",
]


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def snapshot():
    files = {}
    for item in INPUTS:
        root = os.path.join(CAMPAIGN, item)
        if os.path.isfile(root) and not os.path.islink(root):
            files[item] = {"sha256": sha(root), "size": os.path.getsize(root)}
            continue
        for dp, dns, fns in os.walk(root, followlinks=False):
            dns.sort()
            for fn in sorted(fns) + [d for d in dns if os.path.islink(os.path.join(dp, d))]:
                p = os.path.join(dp, fn)
                rel = os.path.relpath(p, CAMPAIGN)
                if os.path.islink(p):
                    files[rel] = {"symlink": os.readlink(p)}
                elif os.path.isfile(p):
                    files[rel] = {"sha256": sha(p), "size": os.path.getsize(p)}
    agg = hashlib.sha256()
    for k in sorted(files):
        agg.update((k + "\0" + json.dumps(files[k], sort_keys=True) + "\n").encode())
    return {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "campaign_dir": CAMPAIGN, "inputs": INPUTS, "n_files": len(files),
            "aggregate_sha256": agg.hexdigest(), "files": files}


def main():
    mode = sys.argv[1]
    if mode == "snapshot":
        snap = snapshot()
        with open(sys.argv[2], "x") as f:
            json.dump(snap, f, indent=1, sort_keys=True)
        print(json.dumps({"n_files": snap["n_files"], "aggregate_sha256": snap["aggregate_sha256"]}))
    elif mode == "compare":
        a = json.load(open(sys.argv[2]))["files"]
        b = json.load(open(sys.argv[3]))["files"]
        changed = sorted(k for k in a if k in b and a[k] != b[k])
        removed = sorted(k for k in a if k not in b)
        added = sorted(k for k in b if k not in a)
        res = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
               "before_files": len(a), "after_files": len(b),
               "changed": changed, "removed": removed, "added": added,
               "all_original_unchanged": not changed and not removed}
        with open(sys.argv[4], "x") as f:
            json.dump(res, f, indent=1)
        print(json.dumps(res))
    else:
        raise SystemExit("unknown mode")


if __name__ == "__main__":
    main()
