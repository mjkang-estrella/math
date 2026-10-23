#!/usr/bin/env python3
"""Read-only verification of this exact selected packet using explicit anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

OUTSIDE = {"MANIFEST.json", "FINAL.json", "REPORT.md", "ANCHORS.txt"}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def fail(message):
    raise ValueError(message)

def local(root, name):
    rel = PurePosixPath(name)
    if rel.is_absolute() or not rel.parts or any(x in ("", ".", "..") for x in rel.parts):
        fail("invalid selection path: " + name)
    q = root.joinpath(*rel.parts)
    cur = root
    for part in rel.parts:
        cur = cur / part
        if cur.is_symlink():
            fail("symlink not allowed: " + name)
    return q

def verify(root, manifest_sha, final_sha, report_sha):
    root = Path(root).resolve()
    supplied = {"MANIFEST.json": manifest_sha, "FINAL.json": final_sha, "REPORT.md": report_sha}
    raw = {}
    for name, wanted in supplied.items():
        if len(wanted) != 64 or any(c not in "0123456789abcdef" for c in wanted):
            fail("expected an explicit lowercase SHA256 for " + name)
        raw[name] = local(root, name).read_bytes()
        if digest(raw[name]) != wanted:
            fail("detached anchor mismatch: " + name)
    manifest = json.loads(raw["MANIFEST.json"])
    final = json.loads(raw["FINAL.json"])
    if manifest.get("format") != "r202-selected-packet-v1":
        fail("unsupported manifest")
    if set(manifest.get("outside_packet", [])) != OUTSIDE:
        fail("outside selection mismatch")
    if final.get("manifest_sha256") != manifest_sha or final.get("report_sha256") != report_sha:
        fail("FINAL does not bind the explicit manifest/report anchors")
    entries = manifest["entries"]
    names = [e["path"] for e in entries]
    if len(names) != len(set(names)) or any(n in OUTSIDE for n in names):
        fail("duplicate or outside selected entry")
    actual = set()
    for here, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            q = Path(here) / name
            if q.is_symlink():
                fail("symlink in packet")
        for name in files:
            q = Path(here) / name
            rel = q.relative_to(root).as_posix()
            if rel not in OUTSIDE:
                actual.add(rel)
    if set(names) != actual:
        fail("exact selected file set differs")
    for e in entries:
        q = local(root, e["path"])
        st = q.stat()
        if not stat.S_ISREG(st.st_mode):
            fail("non-regular selected entry")
        if format(stat.S_IMODE(st.st_mode), "04o") != e["mode"]:
            fail("mode mismatch: " + e["path"])
        b = q.read_bytes()
        if len(b) != e["bytes"] or digest(b) != e["sha256"]:
            fail("content mismatch: " + e["path"])
    frozen_path = final["frozen_path"]
    if frozen_path not in names:
        fail("frozen target not selected")
    if digest(local(root, frozen_path).read_bytes()) != final["frozen_sha256"]:
        fail("frozen target binding mismatch")
    expected_anchors = (
        "FINAL.json " + final_sha + "\n"
        "MANIFEST.json " + manifest_sha + "\n"
        "REPORT.md " + report_sha + "\n"
    )
    if local(root, "ANCHORS.txt").read_text() != expected_anchors:
        fail("detached ANCHORS.txt differs from explicit arguments")
    return {"verified_selected_files": len(entries), "read_only": True}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=str(Path(__file__).resolve().parent))
    ap.add_argument("--manifest-sha256", required=True)
    ap.add_argument("--final-sha256", required=True)
    ap.add_argument("--report-sha256", required=True)
    a = ap.parse_args()
    try:
        result = verify(a.root, a.manifest_sha256, a.final_sha256, a.report_sha256)
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print("ARTIFACT REJECTED:", exc)
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
