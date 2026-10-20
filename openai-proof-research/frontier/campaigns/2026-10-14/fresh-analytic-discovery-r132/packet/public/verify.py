#!/usr/bin/env python3
# MIT License. Read-only integrity verifier for the r132 packet. Byte/inventory checks only; not a mathematical gate.
import argparse
import hashlib
import json
import os
import sys

sys.dont_write_bytecode = True
UNSEALED = {"packet/MANIFEST.json", "FINAL.json", "REPORT.md", "CONTROL-RESULTS.json"}


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def walk(root):
    files, dirs, odd = set(), set(), []
    for d, ds, fs in os.walk(root, followlinks=False):
        rel = os.path.relpath(d, root)
        if rel != ".":
            dirs.add(rel.replace(os.sep, "/"))
        for n in ds + fs:
            p = os.path.join(d, n)
            if os.path.islink(p):
                odd.append(os.path.relpath(p, root))
        for n in fs:
            p = os.path.join(d, n)
            if not os.path.isfile(p) or os.path.islink(p):
                continue
            files.add(os.path.relpath(p, root).replace(os.sep, "/"))
    return files, dirs, odd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--manifest-sha256", required=True)
    ap.add_argument("--final-sha256", required=True)
    ap.add_argument("--report-sha256", required=True)
    ap.add_argument("--project-root", help="optional: also check recorded external inputs are unchanged")
    a = ap.parse_args()
    root = a.root
    errs = []
    man_p = os.path.join(root, "packet/MANIFEST.json")
    fin_p = os.path.join(root, "FINAL.json")
    rep_p = os.path.join(root, "REPORT.md")
    for p, want, name in ((man_p, a.manifest_sha256, "MANIFEST"), (fin_p, a.final_sha256, "FINAL"), (rep_p, a.report_sha256, "REPORT")):
        if not os.path.isfile(p):
            errs.append(f"{name} missing")
        elif sha(p) != want:
            errs.append(f"{name} sha256 mismatch")
    if errs:
        print("FAIL", errs)
        return 1
    man = json.load(open(man_p))
    fin = json.load(open(fin_p))
    if fin.get("manifest_sha256") != a.manifest_sha256:
        errs.append("FINAL does not bind MANIFEST")
    files, dirs, odd = walk(root)
    if odd:
        errs.append(f"symlinks present: {odd}")
    listed = set(man["files"])
    extra = sorted((files - UNSEALED) - listed)
    missing = sorted(listed - files)
    if extra:
        errs.append(f"unlisted files: {extra}")
    if missing:
        errs.append(f"missing files: {missing}")
    for rel in sorted(listed & files):
        p = os.path.join(root, rel)
        rec = man["files"][rel]
        if os.path.getsize(p) != rec["bytes"] or sha(p) != rec["sha256"]:
            errs.append(f"content mismatch: {rel}")
    if set(man.get("directories", [])) != dirs:
        errs.append("directory set mismatch")
    if a.project_root:
        for rel, want in fin.get("external_inputs_sha256", {}).items():
            p = os.path.join(a.project_root, rel)
            if not os.path.isfile(p) or sha(p) != want:
                errs.append(f"external input changed: {rel}")
    if errs:
        print("FAIL")
        for e in errs:
            print(" -", e)
        return 1
    print(f"PASS files={len(listed)} directories={len(dirs)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
