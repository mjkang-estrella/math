"""Hash-bind read-only inputs. Usage: hashbind.py OUT.json PATH [PATH ...]
Paths are given as absolute paths; directories are walked (symlinks not followed)."""
import hashlib, json, os, sys
out = sys.argv[1]
if os.path.exists(out):
    sys.exit("refusing to overwrite " + out)
res = {}
for p in sys.argv[2:]:
    if os.path.isfile(p):
        files = [p]
    else:
        files = []
        for root, dirs, fs in os.walk(p, followlinks=False):
            dirs.sort()
            for f in sorted(fs):
                files.append(os.path.join(root, f))
    for f in files:
        if os.path.islink(f):
            res[f] = "SYMLINK->" + os.readlink(f); continue
        h = hashlib.sha256()
        with open(f, "rb") as fh:
            for b in iter(lambda: fh.read(1 << 20), b""):
                h.update(b)
        res[f] = h.hexdigest()
agg = hashlib.sha256("\n".join(k + " " + v for k, v in sorted(res.items())).encode()).hexdigest()
with open(out, "x") as fh:
    json.dump({"n_files": len(res), "aggregate_sha256": agg, "files": res}, fh, indent=1, sort_keys=True)
print(len(res), agg)
