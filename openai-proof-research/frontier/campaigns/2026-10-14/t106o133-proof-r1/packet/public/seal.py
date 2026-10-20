"""Write packet/MANIFEST.json or FINAL.json for the T106O133 correctness review r1.

    python -B packet/public/seal.py --root ROOT manifest
    python -B packet/public/seal.py --root ROOT final
"""
import argparse
import hashlib
import json
import os
import sys

AUTHOR_ANCHORS = {
    "FINAL.json": "28c1114b783e345e666741df7eadeecccdf6ae92aff898adf4a778b06624d832",
    "packet/MANIFEST.json": "a14d03fcc107582ad645e175e83ed765974805313e43e1958801088a6011cdaa",
    "REPORT.md": "86aa4c953e63da33ec5e7f2263b60df460cf122be84cf9337511cdb1e3f99643",
    "packet/public/frozen-statement.md": "72654d283495baa80aba6349b1b5ebb9a4634ba268d7499a6187ecdd1e311256",
    "packet/public/proof.md": "eb3ea4c63215b75c8edd949903ec35a7d67a11b861cc211f84a05f5139c7a32c",
}


def sha(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def packet_files(root):
    base = os.path.join(root, "packet")
    out = []
    for d, dirs, files in os.walk(base):
        dirs[:] = [x for x in dirs if x != "__pycache__"]
        for f in files:
            rel = os.path.relpath(os.path.join(d, f), base).replace(os.sep, "/")
            if rel != "MANIFEST.json":
                out.append(rel)
    return sorted(out)


def write_manifest(root):
    base = os.path.join(root, "packet")
    files = {r: {"sha256": sha(os.path.join(base, r)), "size": os.path.getsize(os.path.join(base, r))}
             for r in packet_files(root)}
    doc = {"review": "T106O133 correctness r1", "files": files}
    with open(os.path.join(base, "MANIFEST.json"), "w") as fh:
        json.dump(doc, fh, indent=1, sort_keys=True)
        fh.write("\n")
    return sha(os.path.join(base, "MANIFEST.json"))


def write_final(root):
    doc = {
        "candidate": "T106O133",
        "review": "independent correctness r1",
        "verdict": "PASS (full frozen scope: Theorem A, Corollary B decision and search, density form)",
        "pin": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
        "report_sha256": sha(os.path.join(root, "REPORT.md")),
        "manifest_sha256": sha(os.path.join(root, "packet", "MANIFEST.json")),
        "review_sha256": sha(os.path.join(root, "packet", "public", "review.md")),
        "input_fingerprints_sha256": sha(os.path.join(root, "packet", "public", "input-fingerprints.json")),
        "author_anchors": AUTHOR_ANCHORS,
    }
    with open(os.path.join(root, "FINAL.json"), "w") as fh:
        json.dump(doc, fh, indent=1, sort_keys=True)
        fh.write("\n")
    return sha(os.path.join(root, "FINAL.json"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("what", choices=["manifest", "final"])
    a = ap.parse_args()
    print(write_manifest(a.root) if a.what == "manifest" else write_final(a.root))
    return 0


if __name__ == "__main__":
    sys.exit(main())
