#!/usr/bin/env python3
"""Seals the T164F99 contribution-r1 packet once.

Computes packet/MANIFEST.json (all packet files except the manifest itself and
__pycache__), then writes FINAL.json with embedded anchors (manifest, report,
review hashes plus the role-brief immutable-input anchors) and the detached
FINAL.sha256 / REPORT.sha256 files. Run REPORT.md must already exist; run this
exactly once after all packet content is final.
"""
import hashlib, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
PACKET = os.path.join(ROOT, "packet")

BRIEF_ANCHORS = {
    "author_final_sha256": "8bdd4b8849f96c24fca7c91c52006c1b9cb6ee2c6accb44d7e5628746c5ab54f",
    "author_manifest_sha256": "21ce5d125854250c90509dc0d9f4365fcceb97afc6e7e8faa510ea1e509d711e",
    "author_report_sha256": "bdb418b29258b2318310c8876a3beed40a8dc4271e2a1b7ec1d60c072ca6f065",
    "author_scope_sha256": "2a39e2a3410a79812e3e48478fa892d507e163fcd739fd409173219c7c5a23b7",
    "author_proof_sha256": "14d9cd60f44d0bbb8867159b013e7e3026b09cc73208cdce8d3f628dc7175847",
}

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

def main():
    if os.path.exists(os.path.join(ROOT, "FINAL.json")):
        print("FINAL.json already exists; refusing to reseal", file=sys.stderr)
        return 1
    files = {}
    for dirpath, dirnames, filenames in os.walk(PACKET):
        dirnames[:] = [d for d in dirnames if d != "__pycache__"]
        for fn in sorted(filenames):
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, PACKET)
            if rel == "MANIFEST.json":
                continue
            files[rel] = {"sha256": sha256(full), "bytes": os.path.getsize(full)}
    manifest = {"packet": "t164f99-contribution-r1", "files": dict(sorted(files.items()))}
    mpath = os.path.join(PACKET, "MANIFEST.json")
    with open(mpath, "w") as f:
        json.dump(manifest, f, indent=1, sort_keys=True)
        f.write("\n")
    report = os.path.join(ROOT, "REPORT.md")
    if not os.path.exists(report):
        print("REPORT.md missing", file=sys.stderr)
        return 1
    final = {
        "version": 1,
        "status": "SEALED_CONTRIBUTION_REVIEW",
        "review_label": "T164F99 contribution r1",
        "verdict": "TECHNICAL",
        "conditional_on_correctness": True,
        "correctness_gate_assigned": False,
        "count_assigned": False,
        "provider": "Factory Droid",
        "model": "claude-opus-5-5",
        "pin": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
        "manifest_sha256": sha256(mpath),
        "report_sha256": sha256(report),
        "review_sha256": sha256(os.path.join(PACKET, "public", "review.md")),
        "reading_limits_sha256": sha256(os.path.join(PACKET, "public", "reading-limits.md")),
    }
    final.update(BRIEF_ANCHORS)
    fpath = os.path.join(ROOT, "FINAL.json")
    with open(fpath, "w") as f:
        json.dump(final, f, indent=1, sort_keys=True)
        f.write("\n")
    with open(os.path.join(ROOT, "FINAL.sha256"), "w") as f:
        f.write(sha256(fpath) + "  FINAL.json\n")
    with open(os.path.join(ROOT, "REPORT.sha256"), "w") as f:
        f.write(sha256(report) + "  REPORT.md\n")
    print("SEALED files=%d manifest=%s" % (len(files), final["manifest_sha256"]))
    return 0

if __name__ == "__main__":
    sys.exit(main())
