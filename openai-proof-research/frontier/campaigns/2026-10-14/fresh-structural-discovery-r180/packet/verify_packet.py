#!/usr/bin/env python3
"""Read-only selected-packet verification against explicit detached anchors."""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def verify(packet, final, report, anchors):
    manifest = packet / "MANIFEST.json"
    for p, expected in [(final, anchors[0]), (manifest, anchors[1]), (report, anchors[2])]:
        if p.is_symlink() or sha(p) != expected:
            raise ValueError("detached anchor mismatch: " + p.name)
    m = json.loads(manifest.read_text())
    f = json.loads(final.read_text())
    if f["manifest_sha256"] != anchors[1] or f["report_sha256"] != anchors[2]:
        raise ValueError("FINAL links disagree with explicit anchors")
    if m["schema"] != "r180-selected-packet-v1":
        raise ValueError("unexpected manifest schema")
    expected_paths = set()
    for entry in m["files"]:
        rel = entry["path"]
        q = PurePosixPath(rel)
        if q.is_absolute() or ".." in q.parts or q.as_posix() != rel or rel == "MANIFEST.json":
            raise ValueError("unsafe or reserved manifest path")
        if rel in expected_paths:
            raise ValueError("duplicate manifest path")
        expected_paths.add(rel)
        p = packet / rel
        if packet.is_symlink() or any((packet / Path(*q.parts[:i])).is_symlink() for i in range(1, len(q.parts) + 1)):
            raise ValueError("symlink in member path")
        if not p.is_file() or p.stat().st_size != entry["bytes"] or sha(p) != entry["sha256"]:
            raise ValueError("member mismatch: " + rel)
    actual = set()
    for p in packet.rglob("*"):
        if p.is_symlink():
            raise ValueError("symlink in packet")
        if p.is_file() and p != manifest:
            actual.add(p.relative_to(packet).as_posix())
    if actual != expected_paths:
        raise ValueError("packet membership mismatch")
    return len(actual)

if __name__ == "__main__":
    a = argparse.ArgumentParser()
    for key in ["packet", "final", "report", "final-sha", "manifest-sha", "report-sha"]:
        a.add_argument("--" + key, required=True)
    v = a.parse_args()
    try:
        n = verify(Path(v.packet), Path(v.final), Path(v.report), [v.final_sha, v.manifest_sha, v.report_sha])
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as e:
        a.exit(1, "ARTIFACT REJECTED: " + str(e) + "\n")
    print("ARTIFACT MATCH: " + str(n) + " exact selected members; no mathematical gate")
