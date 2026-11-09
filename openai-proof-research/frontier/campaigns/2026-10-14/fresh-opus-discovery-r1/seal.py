#!/usr/bin/env python3
"""One-shot sealer for fresh-opus-discovery-r1. Writes manifests + seal.json + seal.sha256.
Read-only with respect to everything outside this directory's manifest/seal files."""
import hashlib, json, os, sys

ROOT = os.path.dirname(os.path.abspath(__file__))           # fresh-opus-discovery-r1/
REPO = os.path.abspath(os.path.join(ROOT, "..", "..", "..", ".."))
TREE = os.path.join(REPO, "sources", "preprints-tree.json")
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
EXPECTED_TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"

# Family-186 pinned source blobs actually fetched + relied on for context (git blob ids).
SOURCE_RELPATHS = [
    "preprints/A-Sharp-Threshold-Bound-for-Monotone-Graph-Properties-September-25-2026/build/main.tex",
    "preprints/A-Sharp-Threshold-Bound-for-Monotone-Graph-Properties-September-25-2026/build/sections/introduction.tex",
    "preprints/A-Sharp-Threshold-Bound-for-Monotone-Graph-Properties-September-25-2026/build/sections/fourier.tex",
    "preprints/A-Sharp-Threshold-Bound-for-Monotone-Graph-Properties-September-25-2026/build/sections/graph.tex",
    "preprints/A-Sharp-Threshold-Bound-for-Monotone-Graph-Properties-September-25-2026/build/sections/threshold.tex",
    "preprints/A-uniform-influence-bound-for-hypergraph-properties-October-5-2026/build/introduction.tex",
    "preprints/A-uniform-influence-bound-for-hypergraph-properties-October-5-2026/build/fourier.tex",
    "preprints/A-uniform-influence-bound-for-hypergraph-properties-October-5-2026/build/restriction.tex",
    "preprints/A-uniform-influence-bound-for-hypergraph-properties-October-5-2026/build/completion.tex",
]

# Public deliverable files (relative to ROOT). A manifest never lists itself; seal files
# (seal.json/seal.sha256) are the detached anchor and are not listed either.
OUTPUT_RELPATHS = [
    "CHOICE.md", "TARGET.md", "candidate.md", "READING-LIMITS.md",
    "verify.py", "sources-manifest.json",
]

def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

def git_blob_sha1(p):
    data = open(p, "rb").read()
    hdr = b"blob %d\x00" % len(data)
    return hashlib.sha1(hdr + data).hexdigest(), len(data)

def tree_sha256():
    return sha256_file(TREE)

def load_tree_index():
    t = json.load(open(TREE))
    entries = t if isinstance(t, list) else (t.get("tree") or t.get("entries"))
    idx = {}
    for e in entries:
        if isinstance(e, dict) and "path" in e:
            idx[e["path"]] = e.get("sha") or e.get("id") or e.get("oid")
    return idx

def main():
    anchor = tree_sha256()
    idx = load_tree_index()
    sources = []
    for rel in SOURCE_RELPATHS:
        local = os.path.join(ROOT, "private", "src", rel)
        blob, nbytes = git_blob_sha1(local)
        expected = idx.get(rel)
        sources.append({"path": rel, "bytes": nbytes,
                        "git_blob_sha1": blob, "tree_blob_sha1": expected,
                        "blob_matches_tree": (expected == blob)})
    # Write sources-manifest.json FIRST so it exists and is stable before hashing outputs.
    json.dump({"pin": PIN, "tree_sha256": anchor, "sources": sources},
              open(os.path.join(ROOT, "sources-manifest.json"), "w"), indent=2)
    outputs = []
    for rel in OUTPUT_RELPATHS:
        p = os.path.join(ROOT, rel)
        if os.path.exists(p):
            outputs.append({"path": rel, "bytes": os.path.getsize(p), "sha256": sha256_file(p)})
    json.dump({"pin": PIN, "tree_sha256": anchor, "outputs": outputs},
              open(os.path.join(ROOT, "outputs-manifest.json"), "w"), indent=2)
    seal = {
        "package": "fresh-opus-discovery-r1",
        "family": 186,
        "result": "Theorem OPT (optimality of Friedgut-Kalai hypergraph exponent r/(r-1), r>=3)",
        "status": "PROVED; contribution TECHNICAL (not a substantial nominee); count unchanged 17/20",
        "pin": PIN,
        "external_anchor_tree_sha256": anchor,
        "sources": sources,
        "outputs": outputs,
    }
    blob = json.dumps(seal, sort_keys=True, indent=2)
    open(os.path.join(ROOT, "seal.json"), "w").write(blob + "\n")
    sealhash = hashlib.sha256((blob + "\n").encode()).hexdigest()
    open(os.path.join(ROOT, "seal.sha256"), "w").write(sealhash + "\n")
    print("tree_sha256:", anchor, "(matches expected:", anchor == EXPECTED_TREE_SHA256, ")")
    print("sources all blob-match:", all(s["blob_matches_tree"] for s in sources))
    print("outputs sealed:", len(outputs))
    print("seal.sha256:", sealhash)

if __name__ == "__main__":
    main()
