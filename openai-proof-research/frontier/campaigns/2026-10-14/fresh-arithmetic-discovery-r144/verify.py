#!/usr/bin/env python3
"""Read-only exact-packet verification; detached anchors must be supplied externally."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

def sha(data):
    return hashlib.sha256(data).hexdigest()

def verify(root, anchors):
    root = Path(root).resolve()
    for name, expected in anchors.items():
        if len(expected) != 64 or any(c not in "0123456789abcdef" for c in expected):
            raise ValueError("Malformed detached anchor: " + name)
        p = root / name
        if p.is_symlink() or sha(p.read_bytes()) != expected:
            raise ValueError("Detached anchor mismatch: " + name)
    m = json.loads((root / "MANIFEST.json").read_bytes())
    if m.get("format") != "r144-exact-packet-v1":
        raise ValueError("Unknown manifest format")
    names = set()
    for item in m["files"]:
        rel = item["path"]
        q = PurePosixPath(rel)
        if q.is_absolute() or ".." in q.parts or str(q) != rel or not q.parts:
            raise ValueError("Unsafe manifest path")
        if rel in names or rel in {"MANIFEST.json", "REPORT.md", "ANCHORS.json"}:
            raise ValueError("Duplicate/envelope payload path")
        names.add(rel)
        p = root.joinpath(*q.parts)
        if any(root.joinpath(*q.parts[:i]).is_symlink() for i in range(1, len(q.parts)+1)):
            raise ValueError("Symlink payload path")
        data = p.read_bytes()
        if len(data) != item["bytes"] or sha(data) != item["sha256"]:
            raise ValueError("Payload mismatch: " + rel)
    if "FINAL.md" not in names:
        raise ValueError("FINAL absent from payload")
    actual = set()
    for p in root.rglob("*"):
        if p.is_symlink():
            raise ValueError("Unexpected symlink")
        if p.is_file():
            actual.add(p.relative_to(root).as_posix())
    envelopes = {"MANIFEST.json", "REPORT.md", "ANCHORS.json"}
    if actual - envelopes != names:
        raise ValueError("Exact payload membership mismatch")
    return len(names)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", required=True)
    ap.add_argument("--final-sha256", required=True)
    ap.add_argument("--manifest-sha256", required=True)
    ap.add_argument("--report-sha256", required=True)
    a = ap.parse_args()
    try:
        n = verify(a.root, {"FINAL.md": a.final_sha256,
                            "MANIFEST.json": a.manifest_sha256,
                            "REPORT.md": a.report_sha256})
    except (ValueError, OSError, KeyError, TypeError) as exc:
        ap.exit(1, "ARTIFACT VERIFICATION FAILED: " + str(exc) + "\n")
    print("Artifact bytes and exact membership verified for", n, "payload files; no mathematical verdict.")

if __name__ == "__main__":
    main()
