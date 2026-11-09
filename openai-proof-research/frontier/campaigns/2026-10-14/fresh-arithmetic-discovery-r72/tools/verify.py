#!/usr/bin/env python3
"""Read-only verifier for the sealed r72 packet.

Checks, in order, without writing anything:
 1. SHA-256(FINAL.json) equals the detached hash given with --finalhash.
 2. FINAL binds MANIFEST.json, scope-freeze.md and README.md.
 3. Every public file listed in MANIFEST.json exists with the listed SHA-256
    and size, and no unlisted public file is present.
 4. External anchors: every 'ok' entry of source-receipts.json has a Git blob
    SHA-1 equal to the blob in the complete pinned preprints tree (--tree), and
    the retained private copy (if present) hashes to the recorded SHA-256 and
    Git blob.  Private identities listed in MANIFEST are checked if present.
 5. Optional --replay: rerun tools/check_identities.py in a subprocess and
    compare its output with exact-check-results.json.
Exit status 0 iff all checks pass.  Integrity only; not a mathematical proof.
"""
import argparse, hashlib, json, os, subprocess, sys

def sha256(p): return hashlib.sha256(open(p, "rb").read()).hexdigest()
def blob(p):
    d = open(p, "rb").read()
    return hashlib.sha1(b"blob %d\0" % len(d) + d).hexdigest()

ap = argparse.ArgumentParser()
ap.add_argument("--root", required=True)
ap.add_argument("--finalhash", required=True)
ap.add_argument("--tree", default=None, help="path to complete sources/preprints-tree.json")
ap.add_argument("--replay", action="store_true")
a = ap.parse_args()
root = os.path.abspath(a.root)
tree_path = a.tree or os.path.normpath(os.path.join(root, "../../../../sources/preprints-tree.json"))
fails = []
def check(cond, msg):
    if not cond: fails.append(msg)

fp = os.path.join(root, "FINAL.json")
check(os.path.isfile(fp) and sha256(fp) == a.finalhash, "FINAL.json hash differs from detached hash")
if not fails:
    final = json.load(open(fp))
    mp = os.path.join(root, "MANIFEST.json")
    check(sha256(mp) == final["manifest_sha256"], "MANIFEST.json not bound by FINAL")
    check(sha256(os.path.join(root, "scope-freeze.md")) == final["scope_freeze_sha256"], "scope-freeze.md changed")
    check(sha256(os.path.join(root, "README.md")) == final["readme_sha256"], "README.md changed")
    man = json.load(open(mp))
    listed = set()
    for e in man["public"]:
        p = os.path.join(root, e["path"]); listed.add(os.path.normpath(e["path"]))
        if not os.path.isfile(p): fails.append("missing " + e["path"]); continue
        check(os.path.getsize(p) == e["size"] and sha256(p) == e["sha256"], "hash/size mismatch " + e["path"])
    sys.path.insert(0, os.path.join(root, "tools"))
    from make_manifest import public_files  # same enumeration rule as the sealer
    for p in public_files(root):
        check(os.path.normpath(p) in listed, "unlisted public file " + p)
    for e in man.get("private_identities", []):
        p = os.path.join(root, e["path"])
        if os.path.isfile(p): check(sha256(p) == e["sha256"], "private copy changed " + e["path"])
    # external anchors
    if os.path.isfile(tree_path):
        tree = {x["path"]: x for x in json.load(open(tree_path))["tree"]}
        check(len(tree) == 13223, "preprints tree does not have 13223 entries")
        for r in json.load(open(os.path.join(root, "source-receipts.json"))):
            if r.get("status") != "ok": continue
            t = tree.get(r["path"])
            check(t is not None and t["sha"] == r["tree_blob"] == r["computed_blob"],
                  "tree blob anchor mismatch " + r["path"])
            loc = os.path.join(root, r.get("local", ""))
            if r.get("local") and os.path.isfile(loc):
                check(sha256(loc) == r["sha256"] and blob(loc) == r["tree_blob"], "private upstream copy mismatch " + r["path"])
    else:
        fails.append("complete preprints tree not found at " + tree_path)
    if a.replay:
        out = subprocess.run([sys.executable, "-I", "-B", os.path.join(root, "tools", "check_identities.py")],
                             capture_output=True, text=True, cwd=root)
        check(out.returncode == 0 and json.loads(out.stdout) == json.load(open(os.path.join(root, "exact-check-results.json"))),
              "exact-check replay differs")

print(json.dumps({"ok": not fails, "failures": fails}, indent=1))
sys.exit(0 if not fails else 1)
