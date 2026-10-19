#!/usr/bin/env python3
"""Write MANIFEST.json and FINAL.json for this review directory and print FINAL's detached SHA256.

MANIFEST lists every payload except MANIFEST.json, FINAL.json, CONTROLS.json and scratch/.
"""
import hashlib
import json
import os
import stat

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXCLUDED_TOP = {"MANIFEST.json", "FINAL.json", "CONTROLS.json", "scratch"}


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def main():
    files, dirs, dmodes = {}, [], {}
    for dirpath, dirnames, filenames in os.walk(ROOT, followlinks=False):
        rel_dir = os.path.relpath(dirpath, ROOT)
        if rel_dir == ".":
            dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDED_TOP)
            filenames = [n for n in filenames if n not in EXCLUDED_TOP]
        else:
            dirnames.sort()
        for d in dirnames:
            rel = os.path.relpath(os.path.join(dirpath, d), ROOT)
            dirs.append(rel)
            dmodes[rel] = stat.S_IMODE(os.lstat(os.path.join(ROOT, rel)).st_mode)
        for n in sorted(filenames):
            p = os.path.join(dirpath, n)
            st = os.lstat(p)
            if not stat.S_ISREG(st.st_mode):
                raise SystemExit("non-regular payload " + p)
            files[os.path.relpath(p, ROOT)] = {
                "bytes": st.st_size, "mode": stat.S_IMODE(st.st_mode),
                "nlink": st.st_nlink, "sha256": sha256(p)}
    manifest = {"schema": "t195d93-contribution-r1-manifest-v1",
                "directories": sorted(dirs), "directory_modes": dmodes, "files": files}
    with open(os.path.join(ROOT, "MANIFEST.json"), "w") as f:
        json.dump(manifest, f, indent=1, sort_keys=True)
        f.write("\n")
    final = {"schema": "t195d93-contribution-r1-final-v1",
             "candidate": "T195D93",
             "verdict_conditional_on_correctness": "TECHNICAL",
             "gates_assigned_by_reviewer": {"acceptance": None, "count": None, "correctness": None},
             "mathematical_gate": False,
             "review_sha256": sha256(os.path.join(ROOT, "REVIEW.md")),
             "manifest_sha256": sha256(os.path.join(ROOT, "MANIFEST.json"))}
    with open(os.path.join(ROOT, "FINAL.json"), "w") as f:
        json.dump(final, f, indent=1, sort_keys=True)
        f.write("\n")
    print(sha256(os.path.join(ROOT, "FINAL.json")))


if __name__ == "__main__":
    main()
