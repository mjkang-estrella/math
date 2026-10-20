#!/usr/bin/env python3
"""Read-only verifier for the T164F99 contribution-r1 sealed packet.

Usage: python3 verify.py [--root DIR]
  --root defaults to the review root containing this file's grandparent dir
  (i.e. the directory holding packet/, FINAL.json, REPORT.md).

Checks, all read-only:
  1. packet/MANIFEST.json lists exactly the files under packet/ (excluding
     MANIFEST.json itself and __pycache__) with matching SHA-256 and sizes.
  2. FINAL.json embedded anchors match: sha256(packet/MANIFEST.json),
     sha256(REPORT.md), sha256(packet/public/review.md).
  3. REPORT.sha256 and FINAL.sha256 detached files match REPORT.md and
     FINAL.json respectively.
  4. FINAL.json's recorded immutable-input anchors equal the role-brief values
     (author FINAL/MANIFEST/REPORT/scope/proof hashes), and the retained copies
     in packet/private/author/ match those hashes.
Exit 0 on full pass, 1 otherwise. Never opens any file for writing.
"""
import argparse, hashlib, json, os, sys

BRIEF_ANCHORS = {
    "author_final_sha256": "8bdd4b8849f96c24fca7c91c52006c1b9cb6ee2c6accb44d7e5628746c5ab54f",
    "author_manifest_sha256": "21ce5d125854250c90509dc0d9f4365fcceb97afc6e7e8faa510ea1e509d711e",
    "author_report_sha256": "bdb418b29258b2318310c8876a3beed40a8dc4271e2a1b7ec1d60c072ca6f065",
    "author_scope_sha256": "2a39e2a3410a79812e3e48478fa892d507e163fcd739fd409173219c7c5a23b7",
    "author_proof_sha256": "14d9cd60f44d0bbb8867159b013e7e3026b09cc73208cdce8d3f628dc7175847",
}
AUTHOR_COPIES = {
    "author_final_sha256": "private/author/FINAL.json",
    "author_manifest_sha256": "private/author/MANIFEST.json",
    "author_report_sha256": "private/author/REPORT.md",
    "author_scope_sha256": "private/author/scope-freeze.md",
    "author_proof_sha256": "private/author/proof.md",
}

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
    args = ap.parse_args()
    root = os.path.abspath(args.root)
    packet = os.path.join(root, "packet")
    fails = []

    # 1. manifest vs packet tree
    mpath = os.path.join(packet, "MANIFEST.json")
    try:
        manifest = json.load(open(mpath))
        entries = manifest["files"]
    except Exception as e:
        print("FAIL unreadable MANIFEST.json:", e)
        return 1
    actual = {}
    for dirpath, dirnames, filenames in os.walk(packet):
        dirnames[:] = [d for d in dirnames if d != "__pycache__"]
        for fn in filenames:
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, packet)
            if rel == "MANIFEST.json":
                continue
            if os.path.islink(full):
                fails.append("FAIL symlink in packet: " + rel)
                continue
            actual[rel] = {"sha256": sha256(full), "bytes": os.path.getsize(full)}
    if set(actual) != set(entries):
        fails.append("FAIL packet file set differs: extra=%s missing=%s" % (
            sorted(set(actual) - set(entries)), sorted(set(entries) - set(actual))))
    for rel in set(actual) & set(entries):
        if actual[rel]["sha256"] != entries[rel].get("sha256") or actual[rel]["bytes"] != entries[rel].get("bytes"):
            fails.append("FAIL hash mismatch " + rel)

    # 2./3. FINAL/REPORT detached and embedded anchors
    try:
        final = json.load(open(os.path.join(root, "FINAL.json")))
    except Exception as e:
        print("FAIL unreadable FINAL.json:", e)
        return 1
    msha = sha256(mpath)
    rsha = sha256(os.path.join(root, "REPORT.md"))
    vsha = sha256(os.path.join(packet, "public", "review.md"))
    if final.get("manifest_sha256") != msha:
        fails.append("FAIL MANIFEST anchor mismatch")
    if final.get("report_sha256") != rsha:
        fails.append("FAIL REPORT anchor mismatch")
    if final.get("review_sha256") != vsha:
        fails.append("FAIL review anchor mismatch")
    for detached, target, val in (("REPORT.sha256", "REPORT.md", rsha),):
        try:
            if open(os.path.join(root, detached)).read().split()[0] != val:
                fails.append("FAIL detached " + detached)
        except Exception as e:
            fails.append("FAIL detached %s unreadable: %s" % (detached, e))
    try:
        if open(os.path.join(root, "FINAL.sha256")).read().split()[0] != sha256(os.path.join(root, "FINAL.json")):
            fails.append("FAIL detached FINAL.sha256")
    except Exception as e:
        fails.append("FAIL detached FINAL.sha256 unreadable: %s" % e)

    # 4. immutable input anchors vs brief values and retained copies
    for key, want in BRIEF_ANCHORS.items():
        if final.get(key) != want:
            fails.append("FAIL FINAL.json %s != role-brief anchor" % key)
        got = sha256(os.path.join(packet, AUTHOR_COPIES[key]))
        if got != want:
            fails.append("FAIL retained copy %s hash mismatch" % AUTHOR_COPIES[key])

    if fails:
        for f in fails:
            print(f)
        return 1
    print("REVIEW_ARTIFACTS_VERIFIED packet_files=%d root=%s" % (len(actual), os.path.basename(root)))
    return 0

if __name__ == "__main__":
    sys.exit(main())
