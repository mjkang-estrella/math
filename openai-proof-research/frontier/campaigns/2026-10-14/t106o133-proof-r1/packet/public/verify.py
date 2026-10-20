"""Read-only verifier for the T106O133 correctness review r1.

    python -B packet/public/verify.py --root ROOT --project PROJECT --finalhash DETACHED_SHA256

The FINAL.json hash must be supplied detached (from the handoff), never read from this packet.
Checks: FINAL hash; REPORT, MANIFEST, review and fingerprint hashes bound by FINAL; REPORT cites the
MANIFEST hash; exact MANIFEST inventory; pinned git blob SHA-1 of every private source copy against
sources/preprints-tree.json; complete author-root fingerprints (no change, no extra or missing
file); the five explicit author anchors; the context-file hashes. Nothing is written.
Artifact checks are not a mathematical verdict.
"""
import argparse
import hashlib
import json
import os
import re
import sys

EXPECTED_AUTHOR_ANCHORS = {
    "FINAL.json": "28c1114b783e345e666741df7eadeecccdf6ae92aff898adf4a778b06624d832",
    "packet/MANIFEST.json": "a14d03fcc107582ad645e175e83ed765974805313e43e1958801088a6011cdaa",
    "REPORT.md": "86aa4c953e63da33ec5e7f2263b60df460cf122be84cf9337511cdb1e3f99643",
    "packet/public/frozen-statement.md": "72654d283495baa80aba6349b1b5ebb9a4634ba268d7499a6187ecdd1e311256",
    "packet/public/proof.md": "eb3ea4c63215b75c8edd949903ec35a7d67a11b861cc211f84a05f5139c7a32c",
}
PREPRINTS_TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"
P106 = "preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026"
P105 = "preprints/Perfect-completeness-for-2-to-1-games-September-23-2026"


def read(path):
    with open(path, "rb") as fh:
        return fh.read()


def sha(path):
    return hashlib.sha256(read(path)).hexdigest()


def blob(path):
    data = read(path)
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def pinned_path(rel):
    if rel == "src106/README.md":
        return P106 + "/README.md"
    if rel.startswith("src106/"):
        return P106 + "/build/source/" + rel[len("src106/"):]
    if rel == "src105/00-introduction.tex":
        return P105 + "/build/00-introduction.tex"
    return None


def walk(base, skip_pycache=True):
    out = set()
    for d, dirs, files in os.walk(base):
        if skip_pycache:
            dirs[:] = [x for x in dirs if x != "__pycache__"]
        for f in files:
            out.add(os.path.relpath(os.path.join(d, f), base).replace(os.sep, "/"))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--project", required=True)
    ap.add_argument("--finalhash", required=True)
    a = ap.parse_args()
    root, proj = os.path.abspath(a.root), os.path.abspath(a.project)
    fails = []

    def check(cond, msg):
        print(("ok   " if cond else "FAIL ") + msg)
        if not cond:
            fails.append(msg)
        return cond

    if not check(re.fullmatch(r"[0-9a-f]{64}", a.finalhash or "") is not None, "explicit detached FINAL hash supplied"):
        return 1
    if not check(sha(os.path.join(root, "FINAL.json")) == a.finalhash, "FINAL.json matches detached hash"):
        return 1
    final = json.loads(read(os.path.join(root, "FINAL.json")))
    bound = {
        "REPORT.md": final["report_sha256"],
        "packet/MANIFEST.json": final["manifest_sha256"],
        "packet/public/review.md": final["review_sha256"],
        "packet/public/input-fingerprints.json": final["input_fingerprints_sha256"],
    }
    for rel, h in bound.items():
        check(sha(os.path.join(root, rel)) == h, f"{rel} bound by FINAL")
    check(final["manifest_sha256"] in read(os.path.join(root, "REPORT.md")).decode(), "REPORT cites MANIFEST hash")
    check(final.get("author_anchors") == EXPECTED_AUTHOR_ANCHORS, "FINAL author anchors equal explicit anchors")

    man = json.loads(read(os.path.join(root, "packet", "MANIFEST.json")))["files"]
    present = walk(os.path.join(root, "packet")) - {"MANIFEST.json"}
    check(present == set(man), f"MANIFEST inventory exact ({len(man)} files)")
    for rel, ent in sorted(man.items()):
        p = os.path.join(root, "packet", rel)
        if os.path.exists(p):
            check(sha(p) == ent["sha256"] and os.path.getsize(p) == ent["size"], f"packet/{rel}")

    tree_path = os.path.join(proj, "sources", "preprints-tree.json")
    check(sha(tree_path) == PREPRINTS_TREE_SHA256, "complete preprints-tree.json hash")
    tree = {e["path"]: e for e in json.loads(read(tree_path))["tree"]}
    priv = sorted(r for r in man if r.startswith("private/"))
    check(len(priv) == 12, f"12 private pinned source copies ({len(priv)})")
    for rel in priv:
        pin = pinned_path(rel[len("private/"):])
        ent = tree.get(pin) if pin else None
        p = os.path.join(root, "packet", rel)
        check(ent is not None and os.path.exists(p) and blob(p) == ent["sha"], f"pinned blob {rel}")

    fp = json.loads(read(os.path.join(root, "packet", "public", "input-fingerprints.json")))
    check(fp["author_detached_anchors"] == EXPECTED_AUTHOR_ANCHORS, "fingerprint anchors equal explicit anchors")
    aroot = os.path.join(proj, fp["author_root"])
    listed = fp["author_files"]
    check(walk(aroot, skip_pycache=False) == set(listed), f"author root inventory unchanged ({len(listed)} files)")
    changed = [r for r, e in listed.items()
               if not os.path.exists(os.path.join(aroot, r)) or sha(os.path.join(aroot, r)) != e["sha256"]]
    check(not changed, "author root bytes unchanged" + (f": {changed}" if changed else ""))
    for rel, h in EXPECTED_AUTHOR_ANCHORS.items():
        p = os.path.join(aroot, rel)
        check(os.path.exists(p) and sha(p) == h, f"author anchor {rel}")
    for rel, h in fp["context_files"].items():
        p = os.path.join(proj, rel)
        check(os.path.exists(p) and sha(p) == h, f"context {rel}")

    print("VERIFY PASS (artifact checks only)" if not fails else f"VERIFY FAIL ({len(fails)})")
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
