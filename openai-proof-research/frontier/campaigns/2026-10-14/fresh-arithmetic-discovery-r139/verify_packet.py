"""Read-only artifact verifier; explicit detached anchors, no mathematical gates."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

ENVELOPES = {"FINAL.md", "REPORT.md", "private/MANIFEST.json", "ANCHORS.json"}

def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root).resolve(strict=True)
    for name, expected in [("FINAL.md", final_sha), ("private/MANIFEST.json", manifest_sha), ("REPORT.md", report_sha)]:
        if len(expected) != 64 or any(c not in "0123456789abcdef" for c in expected):
            raise ValueError("invalid explicit SHA256 anchor")
        p = root / name
        if p.is_symlink() or not p.is_file() or digest(p) != expected:
            raise ValueError("detached anchor mismatch: " + name)
    manifest = json.loads((root / "private/MANIFEST.json").read_text())
    if manifest.get("format") != "r139-exact-selected-packet-v1":
        raise ValueError("wrong manifest format")
    selected = set()
    for row in manifest["files"]:
        name = row["path"]
        q = PurePosixPath(name)
        if q.is_absolute() or ".." in q.parts or str(q) != name or name in ENVELOPES or name in selected:
            raise ValueError("unsafe/duplicate/envelope payload entry")
        selected.add(name)
        p = root / name
        if p.is_symlink() or not p.is_file() or not p.resolve().is_relative_to(root):
            raise ValueError("missing or unsafe payload: " + name)
        if p.stat().st_size != row["bytes"] or digest(p) != row["sha256"]:
            raise ValueError("payload mismatch: " + name)
    actual = set()
    for p in root.rglob("*"):
        if p.is_symlink():
            raise ValueError("symlink in packet")
        if p.is_file():
            actual.add(p.relative_to(root).as_posix())
    if actual - ENVELOPES != selected:
        raise ValueError("selected-file inventory mismatch")
    return {"artifact_verification": "MATCH", "payload_files": len(selected),
            "mathematical_gate": "none"}

if __name__ == "__main__":
    a = argparse.ArgumentParser(description=__doc__)
    a.add_argument("--root", required=True)
    a.add_argument("--final-sha", required=True)
    a.add_argument("--manifest-sha", required=True)
    a.add_argument("--report-sha", required=True)
    x = a.parse_args()
    print(json.dumps(verify(x.root, x.final_sha, x.manifest_sha, x.report_sha), sort_keys=True))
