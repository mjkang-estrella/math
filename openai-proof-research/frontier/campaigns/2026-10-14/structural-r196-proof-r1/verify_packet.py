#!/usr/bin/env python3
"""Read-only exact-selection verifier. Supply independently held SHA256 anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_path(name):
    p = PurePosixPath(name)
    return bool(name) and not p.is_absolute() and name == p.as_posix() and all(
        x not in ("", ".", "..") for x in p.parts
    )


def verify(root, anchors):
    require(not root.is_symlink() and root.is_dir(), "root must be a real directory")
    require(all(re.fullmatch(r"[0-9a-f]{64}", v) for v in anchors.values()), "invalid explicit anchor")
    for name in ("FINAL.md", "MANIFEST.json", "REPORT.md"):
        p = root / name
        require(p.is_file() and not p.is_symlink(), "missing or linked detached carrier: " + name)
        require(digest(p.read_bytes()) == anchors[name], "detached anchor mismatch: " + name)
    m = json.loads((root / "MANIFEST.json").read_text())
    require(set(m) == {"schema", "selection", "directories", "detached_modes", "seal_policy"}, "unexpected manifest fields")
    require(m["schema"] == "structural196-review-exact-v1", "unsupported manifest schema")
    require(m["seal_policy"] == "one final seal; report outside selection; explicit detached anchors required", "unexpected seal policy")
    selected = m["selection"]
    detached = {"MANIFEST.json", "REPORT.md", "ANCHORS.json"}
    require(isinstance(selected, dict) and "FINAL.md" in selected, "missing FINAL selection")
    require(not (set(selected) & detached), "detached carrier selected")
    require(all(safe_path(n) for n in selected), "unsafe selected path")
    require(set(m["detached_modes"]) == detached, "unexpected detached modes")
    dirs = m["directories"]
    require(isinstance(dirs, dict) and "." in dirs, "missing root mode")
    require(all(n == "." or safe_path(n) for n in dirs), "unsafe directory path")
    actual_files, actual_dirs = {}, {".": stat.S_IMODE(root.lstat().st_mode)}
    for base, dirnames, filenames in os.walk(root, followlinks=False):
        for name in dirnames + filenames:
            p = Path(base) / name
            info = p.lstat()
            rel = p.relative_to(root).as_posix()
            require(not stat.S_ISLNK(info.st_mode), "symlink rejected: " + rel)
            if stat.S_ISDIR(info.st_mode):
                actual_dirs[rel] = stat.S_IMODE(info.st_mode)
            else:
                require(stat.S_ISREG(info.st_mode), "special entry rejected: " + rel)
                actual_files[rel] = stat.S_IMODE(info.st_mode)
    require(set(actual_files) == set(selected) | detached, "exact file selection mismatch")
    require(actual_dirs == dirs, "directory selection or mode mismatch")
    for name, mode in m["detached_modes"].items():
        require(actual_files[name] == mode, "detached mode mismatch: " + name)
    for name, entry in selected.items():
        require(set(entry) == {"bytes", "sha256", "mode"}, "invalid selected entry: " + name)
        require(actual_files[name] == entry["mode"], "selected mode mismatch: " + name)
        b = (root / name).read_bytes()
        require(len(b) == entry["bytes"] and digest(b) == entry["sha256"], "selected bytes mismatch: " + name)
    carrier = (root / "ANCHORS.json").read_bytes()
    require(carrier == (json.dumps(anchors, indent=2) + "\n").encode(), "anchor carrier differs from explicit anchors")
    return {"integrity": "PASS", "selected_files": len(selected), "directories": len(dirs),
            "exact_selection": True, "modes": True, "read_only": True,
            "mathematical_grade_from_verifier": None}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", required=True, type=Path)
    ap.add_argument("--final-sha256", required=True)
    ap.add_argument("--manifest-sha256", required=True)
    ap.add_argument("--report-sha256", required=True)
    a = ap.parse_args()
    anchors = {"FINAL.md": a.final_sha256, "MANIFEST.json": a.manifest_sha256, "REPORT.md": a.report_sha256}
    try:
        print(json.dumps(verify(a.root.absolute(), anchors), sort_keys=True))
    except (ValueError, OSError, TypeError, KeyError) as e:
        print("FAIL: " + str(e), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
