"""Read-only exact-selection verification; explicit detached anchors are required.

This checks artifact integrity and file modes, never mathematical correctness.
Only the declared envelope files and the separate tiny controls directory are
outside the selected packet. No output file is written by this program.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import stat


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def need(condition, message):
    if not condition:
        raise ValueError(message)


def verify(root, anchors):
    reserved = {"FINAL.md", "MANIFEST.json", "REPORT.md", "ANCHORS.json", "SEAL-CHECK.json"}
    need(root.is_dir() and not root.is_symlink(), "invalid packet root")
    for name, anchor in anchors.items():
        need(len(anchor) == 64 and all(c in "0123456789abcdef" for c in anchor), "invalid explicit anchor")
        p = root / name
        need(p.is_file() and not p.is_symlink(), "missing envelope: " + name)
        need(digest(p) == anchor, "detached anchor mismatch: " + name)
        need(stat.S_IMODE(p.stat().st_mode) == 0o444, "envelope mode mismatch: " + name)
    need(json.loads((root / "ANCHORS.json").read_text()) == anchors, "detached anchor record mismatch")
    manifest = json.loads((root / "MANIFEST.json").read_text())
    selected = json.loads((root / "SELECTION.json").read_text())
    names = [e["path"] for e in manifest["files"]]
    need(names == sorted(set(names)) == selected["files"], "selection/manifest disagreement")
    need(selected["reserved_files"] == sorted(reserved), "unexpected envelope exclusions")
    need(selected["reserved_subtree"] == "controls", "unexpected subtree exclusion")
    for item in manifest["files"]:
        rel = PurePosixPath(item["path"])
        need(not rel.is_absolute() and ".." not in rel.parts and rel.parts[0] != "controls", "unsafe selected path")
        p = root.joinpath(*rel.parts)
        need(p.is_file() and not p.is_symlink(), "missing/nonregular selected file: " + str(rel))
        need(p.stat().st_size == item["bytes"] and digest(p) == item["sha256"], "selected bytes mismatch: " + str(rel))
        need(stat.S_IMODE(p.stat().st_mode) == item["mode"], "selected mode mismatch: " + str(rel))
    actual_files, actual_dirs = set(), set()
    for base, dirs, files in os.walk(root, followlinks=False):
        base = Path(base)
        if base == root and "controls" in dirs:
            dirs.remove("controls")
        need(not any((base / d).is_symlink() for d in dirs), "symlink directory")
        actual_dirs.add(base.relative_to(root).as_posix())
        for name in files:
            p = base / name
            need(not p.is_symlink(), "symlink file")
            actual_files.add(p.relative_to(root).as_posix())
    need(actual_files - reserved == set(names), "extra or missing selected file")
    need(actual_dirs == {d["path"] for d in manifest["directories"]}, "directory selection mismatch")
    for d in manifest["directories"]:
        need(stat.S_IMODE((root / d["path"]).stat().st_mode) == d["mode"], "directory mode mismatch: " + d["path"])
    return {"artifact_check": "exact selected bytes, modes and detached anchors match", "files": len(names), "mathematical_gate": False}


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", required=True, type=Path)
    p.add_argument("--final-sha256", required=True)
    p.add_argument("--manifest-sha256", required=True)
    p.add_argument("--report-sha256", required=True)
    a = p.parse_args()
    try:
        print(json.dumps(verify(a.root, {"FINAL.md": a.final_sha256, "MANIFEST.json": a.manifest_sha256, "REPORT.md": a.report_sha256}), sort_keys=True))
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as e:
        raise SystemExit("artifact verification failed: " + str(e))
