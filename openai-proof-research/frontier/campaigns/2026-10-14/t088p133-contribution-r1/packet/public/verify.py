#!/usr/bin/env python3
"""Read-only verifier for the T088P133 contribution-review packet.

Checks, without writing anything:
  1. packet/MANIFEST.json matches every file under packet/ (except MANIFEST.json itself);
  2. FINAL.json matches the detached hash given by --final-sha256;
  3. REPORT.md matches the detached hash given by --report-sha256;
  4. MANIFEST.json matches --manifest-sha256.
Usage: python3 verify.py --root ROOT --manifest-sha256 M --final-sha256 F --report-sha256 R
Exit 0 and print PASS on success; print FAIL lines and exit 1 otherwise.
"""
import argparse, hashlib, json, os, sys


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--manifest-sha256", required=True)
    ap.add_argument("--final-sha256", required=True)
    ap.add_argument("--report-sha256", required=True)
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    fails = []

    mpath = os.path.join(root, "packet", "MANIFEST.json")
    if sha256(mpath) != a.manifest_sha256:
        fails.append("MANIFEST sha256 mismatch")
    manifest = json.load(open(mpath))
    files = manifest["files"]

    seen = set()
    for base in ("packet", "private", "work"):
        for dirpath, dirnames, filenames in os.walk(os.path.join(root, base)):
            dirnames.sort()
            for fn in sorted(filenames):
                p = os.path.join(dirpath, fn)
                rel = os.path.relpath(p, root)
                if rel == os.path.join("packet", "MANIFEST.json"):
                    continue
                seen.add(rel)
                rec = files.get(rel)
                if rec is None:
                    fails.append("unlisted file %s" % rel)
                elif sha256(p) != rec["sha256"] or os.path.getsize(p) != rec["size"]:
                    fails.append("hash/size mismatch %s" % rel)
    for rel in files:
        if rel not in seen:
            fails.append("missing file %s" % rel)

    for path, want, name in ((os.path.join(root, "FINAL.json"), a.final_sha256, "FINAL"),
                             (os.path.join(root, "REPORT.md"), a.report_sha256, "REPORT")):
        if not os.path.exists(path) or sha256(path) != want:
            fails.append("%s sha256 mismatch" % name)

    n = len(files)
    if fails:
        print("FAIL %s" % fails)
        return 1
    print("PASS files=%d" % n)
    return 0


if __name__ == "__main__":
    sys.exit(main())
