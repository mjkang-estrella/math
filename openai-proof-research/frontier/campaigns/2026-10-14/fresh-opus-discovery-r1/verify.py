#!/usr/bin/env python3
"""Read-only identity verifier for fresh-opus-discovery-r1. Fails closed.

External anchor = the pinned-tree SHA256 stipulated by the campaign
(eeecc1da...e09b) AND the detached seal hash passed via --anchor.
Usage:  python3 -B verify.py --anchor=<seal.sha256 hex>
Exit 0 = all checks pass; exit 1 = any mismatch / wrong anchor / missing file.
Writes nothing."""
import hashlib, json, os, sys

ROOT = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(ROOT, "..", "..", "..", ".."))
TREE = os.path.join(REPO, "sources", "preprints-tree.json")
EXPECTED_TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"

def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

def git_blob_sha1(p):
    data = open(p, "rb").read()
    return hashlib.sha1(b"blob %d\x00" % len(data) + data).hexdigest()

def fail(msg):
    print("FAIL:", msg); sys.exit(1)

def main():
    anchor = None
    for a in sys.argv[1:]:
        if a.startswith("--anchor="):
            anchor = a.split("=", 1)[1].strip()
    if not anchor:
        fail("no --anchor given")
    # 0. external anchor: pinned tree hash must equal the stipulated constant.
    th = sha256_file(TREE)
    if th != EXPECTED_TREE_SHA256:
        fail(f"pinned tree sha256 {th} != stipulated {EXPECTED_TREE_SHA256}")
    # 1. detached seal hash must match --anchor and seal.json.
    seal_path = os.path.join(ROOT, "seal.json")
    recorded = open(os.path.join(ROOT, "seal.sha256")).read().strip()
    blob = open(seal_path).read()
    actual = hashlib.sha256(blob.encode()).hexdigest()
    if actual != recorded:
        fail("seal.json sha256 != seal.sha256")
    if recorded != anchor:
        fail("--anchor does not match seal.sha256 (wrong/foreign anchor)")
    seal = json.loads(blob)
    if seal.get("pin") != PIN:
        fail("seal pin mismatch")
    if seal.get("external_anchor_tree_sha256") != EXPECTED_TREE_SHA256:
        fail("seal external anchor mismatch")
    # 2. sources: local blobs must match the pinned tree and the manifest.
    sm = json.load(open(os.path.join(ROOT, "sources-manifest.json")))
    t = json.load(open(TREE)); entries = t if isinstance(t, list) else (t.get("tree") or t.get("entries"))
    idx = {e["path"]: (e.get("sha") or e.get("id") or e.get("oid")) for e in entries if isinstance(e, dict) and "path" in e}
    man = {s["path"]: s for s in sm["sources"]}
    if set(man) != {s["path"] for s in seal["sources"]}:
        fail("source set mismatch between seal.json and sources-manifest.json")
    for path, s in man.items():
        local = os.path.join(ROOT, "private", "src", path)
        if not os.path.exists(local):
            fail(f"missing source {path}")
        if git_blob_sha1(local) != s["git_blob_sha1"]:
            fail(f"source blob changed {path}")
        if idx.get(path) != s["git_blob_sha1"]:
            fail(f"source {path} does not match pinned tree blob")
    # 3. outputs: hashes must match the manifest and seal.
    om = {o["path"]: o for o in json.load(open(os.path.join(ROOT, "outputs-manifest.json")))["outputs"]}
    if set(om) != {o["path"] for o in seal["outputs"]}:
        fail("output set mismatch between seal.json and outputs-manifest.json")
    for path, o in om.items():
        p = os.path.join(ROOT, path)
        if not os.path.exists(p):
            fail(f"missing output {path}")
        if sha256_file(p) != o["sha256"]:
            fail(f"output changed {path}")
    print("OK: anchor, seal, %d sources (blob-verified vs pinned tree), %d outputs all match."
          % (len(man), len(om)))
    sys.exit(0)

if __name__ == "__main__":
    main()
