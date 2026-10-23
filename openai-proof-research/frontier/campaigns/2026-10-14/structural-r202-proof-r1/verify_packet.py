#!/usr/bin/env python3
"""Read-only artifact verification with explicit detached FINAL/MANIFEST/REPORT anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

OUTSIDE = {"FINAL.json", "MANIFEST.json", "REPORT.md", "ANCHORS.txt"}
FORMAT = "structural-r202-review-packet-v1"

def digest(data):
    return hashlib.sha256(data).hexdigest()

def require(test, message):
    if not test:
        raise ValueError(message)

def local(root, name, directory=False):
    if directory and name == ".":
        return root
    rel = PurePosixPath(name)
    require(bool(rel.parts) and not rel.is_absolute() and rel.as_posix() == name
            and all(x not in ("", ".", "..") for x in rel.parts), "invalid relative path")
    p = root
    for part in rel.parts:
        p = p / part
        require(not p.is_symlink(), "symlink: " + name)
    return p

def mode(p):
    return format(stat.S_IMODE(p.lstat().st_mode), "04o")

def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root).absolute()
    require(not root.is_symlink() and root.is_dir(), "root is not a real directory")
    raw = {}
    for name, wanted in [("FINAL.json", final_sha), ("MANIFEST.json", manifest_sha), ("REPORT.md", report_sha)]:
        require(len(wanted) == 64 and all(c in "0123456789abcdef" for c in wanted), "explicit lowercase SHA256 required")
        p = local(root, name)
        require(stat.S_ISREG(p.lstat().st_mode), "outside file is not regular")
        raw[name] = p.read_bytes()
        require(digest(raw[name]) == wanted, "detached anchor mismatch: " + name)
    m = json.loads(raw["MANIFEST.json"])
    f = json.loads(raw["FINAL.json"])
    require(m["format"] == FORMAT, "unsupported manifest format")
    require(f["manifest_sha256"] == manifest_sha and f["report_sha256"] == report_sha,
            "FINAL anchor binding differs")
    entries, directories, outside = m["files"], m["directories"], m["outside_files"]
    names = [e["path"] for e in entries]
    dnames = [e["path"] for e in directories]
    onames = [e["path"] for e in outside]
    require(len(names) == len(set(names)) and not (set(names) & OUTSIDE), "duplicate or outside selected file")
    require(len(dnames) == len(set(dnames)) and "." in dnames, "invalid selected directory set")
    require(len(onames) == len(set(onames)) and set(onames) == OUTSIDE, "outside file set differs")
    actual_files, actual_dirs = set(), {"."}
    for here, ds, fs in os.walk(root, followlinks=False):
        for n in ds + fs:
            p = Path(here) / n
            st = p.lstat()
            rel = p.relative_to(root).as_posix()
            require(not stat.S_ISLNK(st.st_mode), "symlink in packet: " + rel)
            if stat.S_ISDIR(st.st_mode):
                actual_dirs.add(rel)
            elif stat.S_ISREG(st.st_mode):
                actual_files.add(rel)
            else:
                raise ValueError("nonregular entry: " + rel)
    require(actual_files == set(names) | OUTSIDE, "exact file set differs")
    require(actual_dirs == set(dnames), "exact directory set differs")
    for e in directories:
        p = local(root, e["path"], directory=True)
        require(p.is_dir() and mode(p) == e["mode"], "directory mode differs: " + e["path"])
    for e in outside:
        p = local(root, e["path"])
        require(mode(p) == e["mode"], "outside-file mode differs: " + e["path"])
    for e in entries:
        p = local(root, e["path"])
        require(mode(p) == e["mode"], "selected file mode differs: " + e["path"])
        b = p.read_bytes()
        require(len(b) == e["bytes"] and digest(b) == e["sha256"], "selected file bytes differ: " + e["path"])
    target = f["selected_target"]
    require(target["path"] in names, "target is not selected")
    require(digest(local(root, target["path"]).read_bytes()) == target["sha256"], "target binding differs")
    expected = ("FINAL.json " + final_sha + "\nMANIFEST.json " + manifest_sha
                + "\nREPORT.md " + report_sha + "\n")
    require(local(root, "ANCHORS.txt").read_text() == expected, "ANCHORS differs from explicit arguments")
    return {"artifact_verified": True, "selected_files": len(entries),
            "directories_including_root": len(directories), "outside_files": len(outside), "read_only": True}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(Path(__file__).absolute().parent))
    parser.add_argument("--final-sha256", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--report-sha256", required=True)
    args = parser.parse_args()
    try:
        result = verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256)
    except (ValueError, OSError, KeyError, TypeError) as error:
        print("ARTIFACT REJECTED:", error)
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
