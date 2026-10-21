#!/usr/bin/env python3
"""Read-only artifact verifier. Three detached SHA256 anchors are mandatory.
No mathematical correctness or contribution claim is tested here.
"""
import argparse, hashlib, json, re
from pathlib import Path, PurePosixPath

ENVELOPES = {"FINAL.md", "REPORT.md", "ANCHORS.json", "private/MANIFEST.json"}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def safe_file(root, name):
    q = PurePosixPath(name)
    if q.is_absolute() or not q.parts or any(x in ("..", ".") for x in q.parts) or q.as_posix() != name:
        raise ValueError("unsafe manifest path")
    p = root
    for part in q.parts:
        p = p / part
        if p.is_symlink():
            raise ValueError("symlink forbidden")
    if not p.is_file():
        raise ValueError("missing payload: " + name)
    return p

def verify(root, final_sha256, manifest_sha256, report_sha256):
    root = Path(root).resolve(strict=True)
    for name, anchor in [("FINAL.md", final_sha256), ("private/MANIFEST.json", manifest_sha256), ("REPORT.md", report_sha256)]:
        if not re.fullmatch("[0-9a-f]{64}", anchor):
            raise ValueError("explicit SHA256 anchor required")
        if digest(safe_file(root, name).read_bytes()) != anchor:
            raise ValueError("detached anchor mismatch: " + name)
    doc = json.loads((root / "private/MANIFEST.json").read_text())
    if doc.get("format") != "r138-exact-payload-v1":
        raise ValueError("manifest format mismatch")
    expected = set()
    for entry in doc["files"]:
        name = entry["path"]
        if name in ENVELOPES or name in expected:
            raise ValueError("duplicate or envelope payload")
        p = safe_file(root, name)
        expected.add(name)
        b = p.read_bytes()
        if len(b) != entry["bytes"] or digest(b) != entry["sha256"]:
            raise ValueError("payload mismatch: " + name)
    actual = set()
    for p in root.rglob("*"):
        if p.is_symlink():
            raise ValueError("symlink in packet")
        if p.is_file():
            name = p.relative_to(root).as_posix()
            if name not in ENVELOPES:
                actual.add(name)
    if actual != expected:
        raise ValueError("packet membership mismatch")
    return {"artifact_integrity": "matched supplied anchors", "payload_files": len(expected), "mathematical_gate": False}

if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", required=True)
    p.add_argument("--final-sha256", required=True)
    p.add_argument("--manifest-sha256", required=True)
    p.add_argument("--report-sha256", required=True)
    args = p.parse_args()
    print(json.dumps(verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256), sort_keys=True))
