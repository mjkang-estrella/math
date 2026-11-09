import hashlib, os, sys
base = sys.argv[1]; out = sys.argv[2]
targets = ["cycramsey-root-check-r1.json", "expanded-corpus-r112", "cycramsey-parent-check-r1"]
lines = []
for t in targets:
    p = os.path.join(base, t)
    if os.path.isfile(p):
        files = [p]
    else:
        files = []
        for d, ds, fs in os.walk(p):
            ds[:] = sorted(x for x in ds if x not in (".lake",))
            for f in sorted(fs):
                files.append(os.path.join(d, f))
    for f in files:
        h = hashlib.sha256()
        with open(f, "rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
        lines.append(f"{h.hexdigest()}  {os.path.relpath(f, base)}")
open(out, "w").write("\n".join(lines) + "\n")
print(len(lines), "files hashed")
