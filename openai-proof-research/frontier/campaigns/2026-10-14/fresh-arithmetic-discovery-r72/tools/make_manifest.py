#!/usr/bin/env python3
"""Seal the public packet: MANIFEST.json lists every public file with SHA-256
and size, plus the SHA-256 of every private retained copy (identity only).
FINAL.json binds MANIFEST.json and the frozen scope. Usage: make_manifest.py ROOT
"""
import hashlib, json, os, sys, datetime

EXCLUDE_TOP = {"private", "integrity", "MANIFEST.json", "FINAL.json"}

def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()

def public_files(root):
    out = []
    for dp, dn, fn in os.walk(root):
        rel = os.path.relpath(dp, root)
        parts = [] if rel == "." else rel.split(os.sep)
        if parts and parts[0] in EXCLUDE_TOP: dn[:] = []; continue
        dn[:] = [d for d in dn if d != "__pycache__" and not (rel == "." and d in EXCLUDE_TOP)]
        for f in fn:
            r = os.path.normpath(os.path.join(rel, f))
            if r in EXCLUDE_TOP or f.endswith(".pyc"): continue
            out.append(r)
    return sorted(out)

def private_files(root):
    out = []
    base = os.path.join(root, "private")
    for dp, dn, fn in os.walk(base):
        dn[:] = [d for d in dn if d != "__pycache__"]
        for f in fn:
            out.append(os.path.relpath(os.path.join(dp, f), root))
    return sorted(out)

if __name__ == "__main__":
    root = sys.argv[1]
    man = {"packet": "fresh-arithmetic-discovery-r72",
           "pinned_commit": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
           "public": [{"path": p, "sha256": sha(os.path.join(root, p)),
                       "size": os.path.getsize(os.path.join(root, p))} for p in public_files(root)],
           "private_identities": [{"path": p, "sha256": sha(os.path.join(root, p))}
                                  for p in private_files(root)]}
    mp = os.path.join(root, "MANIFEST.json")
    with open(mp, "w") as f: json.dump(man, f, indent=1, sort_keys=True); f.write("\n")
    final = {"manifest_sha256": sha(mp),
             "scope_freeze_sha256": sha(os.path.join(root, "scope-freeze.md")),
             "readme_sha256": sha(os.path.join(root, "README.md")),
             "sealed_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}
    fp = os.path.join(root, "FINAL.json")
    with open(fp, "w") as f: json.dump(final, f, indent=1, sort_keys=True); f.write("\n")
    print("public files:", len(man["public"]), "private identities:", len(man["private_identities"]))
    print("MANIFEST sha256:", final["manifest_sha256"])
    print("FINAL sha256:", sha(fp))
