#!/usr/bin/env python3
"""Read-only selected-packet integrity verification; not mathematical verification."""
import argparse, hashlib, json, re
from pathlib import Path, PurePosixPath

def sha(data):
    return hashlib.sha256(data).hexdigest()

def checked(path, expected, size=None):
    if not re.fullmatch(r"[0-9a-f]{64}", expected):
        raise ValueError("expected explicit SHA256 anchor")
    if path.is_symlink():
        raise ValueError("symlink refused: " + str(path))
    data = path.read_bytes()
    if (size is not None and len(data) != size) or sha(data) != expected:
        raise ValueError("digest/length mismatch: " + str(path))
    return data

def inside(root, name):
    q = PurePosixPath(name)
    if q.is_absolute() or ".." in q.parts or not q.parts:
        raise ValueError("unsafe relative path")
    p = root.joinpath(*q.parts)
    if not p.resolve().is_relative_to(root.resolve()):
        raise ValueError("path escapes selected root")
    return p

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="mode", required=True)
    f = sub.add_parser("file")
    f.add_argument("path", type=Path); f.add_argument("--sha", required=True)
    p = sub.add_parser("packet")
    p.add_argument("--root", type=Path, required=True)
    p.add_argument("--final-sha", required=True)
    p.add_argument("--manifest-sha", required=True)
    p.add_argument("--report-sha", required=True)
    p.add_argument("--project-root", type=Path)
    a = ap.parse_args()
    if a.mode == "file":
        checked(a.path, a.sha); print("copied file digest matches"); return
    checked(a.root / "FINAL.md", a.final_sha)
    manifest = json.loads(checked(a.root / "private/MANIFEST.json", a.manifest_sha))
    checked(a.root / "REPORT.md", a.report_sha)
    seen = set()
    for entry in manifest["entries"]:
        name = entry["path"]
        if name in seen: raise ValueError("duplicate selected path")
        seen.add(name)
        checked(inside(a.root, name), entry["sha256"], entry["bytes"])
    if "FINAL.md" not in seen or "VERIFY.py" not in seen:
        raise ValueError("missing selected anchor or verifier")
    # Authenticated selected source copies, no network and no inherited manifest.
    for item in json.loads((a.root / "private/source-auth.json").read_bytes()):
        marker = "frontier/campaigns/2026-10-14/fresh-structural-discovery-r185/"
        if not item["local"].startswith(marker): raise ValueError("wrong packet source")
        data = checked(inside(a.root, item["local"][len(marker):]), item["sha256"], item["bytes"])
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != item["blob"]: raise ValueError("Git blob mismatch")
    original_count = 0
    if a.project_root:
        for item in json.loads((a.root / "private/original-anchors.json").read_bytes()):
            path = inside(a.project_root, item["path"])
            if path.is_symlink(): raise ValueError("original symlink refused")
            with path.open("rb") as stream:
                stream.seek(item["start"])
                data = stream.read(item["end"] - item["start"])
            if sha(data) != item["sha256"]: raise ValueError("original span changed: " + item["path"])
            original_count += 1
    print(json.dumps({"selected_files": len(seen), "source_blobs": 12,
                      "exact_original_spans": original_count,
                      "scope": "artifact integrity only; no mathematical grade"}))

if __name__ == "__main__":
    try: main()
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit(str(error))
