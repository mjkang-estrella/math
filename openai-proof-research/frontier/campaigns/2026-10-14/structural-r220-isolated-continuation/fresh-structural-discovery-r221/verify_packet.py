"""Read-only exact-selection/mode verifier. All three SHA256 anchors are supplied by the caller."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat

OUTSIDE = {"MANIFEST.json", "REPORT.md", "ANCHORS.json"}
OUTSIDE_MODES = {"MANIFEST.json": 0o600, "REPORT.md": 0o644, "ANCHORS.json": 0o600}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def inventory(root):
    require(root.is_dir() and not root.is_symlink(), "root is not a real directory")
    files, dirs = {}, {"": stat.S_IMODE(root.stat().st_mode)}
    for base, names, leaves in os.walk(root, followlinks=False):
        for name in names + leaves:
            path = Path(base) / name
            rel = path.relative_to(root).as_posix()
            mode = path.lstat().st_mode
            require(not stat.S_ISLNK(mode), "symlink: " + rel)
            if stat.S_ISDIR(mode):
                dirs[rel] = stat.S_IMODE(mode)
            else:
                require(stat.S_ISREG(mode), "nonregular file: " + rel)
                files[rel] = path
    return files, dirs

def check_entries(root, manifest):
    files, dirs = inventory(root)
    expected = {entry["path"]: entry for entry in manifest["files"]}
    require(len(expected) == len(manifest["files"]), "duplicate selected path")
    require(not (set(expected) & OUTSIDE), "outside file selected in payload")
    require(set(files) - OUTSIDE == set(expected), "exact file selection differs")
    expected_dirs = {entry["path"]: entry["mode"] for entry in manifest["directories"]}
    require(len(expected_dirs) == len(manifest["directories"]), "duplicate directory")
    require(dirs == expected_dirs, "directory selection or mode differs")
    for name, entry in expected.items():
        path = files[name]
        require(path.stat().st_size == entry["bytes"], "size: " + name)
        require(stat.S_IMODE(path.stat().st_mode) == entry["mode"], "mode: " + name)
        require(digest(path) == entry["sha256"], "hash: " + name)
    for name in set(files) & OUTSIDE:
        require(stat.S_IMODE(files[name].stat().st_mode) == OUTSIDE_MODES[name], "outside mode: " + name)
    return {"selected_files": len(expected), "directories": len(dirs)}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--final-sha", required=True)
    parser.add_argument("--manifest-sha", required=True)
    parser.add_argument("--report-sha")
    parser.add_argument("--payload-only", action="store_true")
    args = parser.parse_args()
    root = args.root.absolute()
    inventory(root)  # Reject symlinks before following any packet path.
    require(digest(root / "MANIFEST.json") == args.manifest_sha, "detached MANIFEST anchor differs")
    require(digest(root / "FINAL.md") == args.final_sha, "detached FINAL anchor differs")
    manifest = json.loads((root / "MANIFEST.json").read_text())
    require(manifest["schema"] == "r221-exact-selected-packet-v1", "schema")
    result = check_entries(root, manifest)
    if args.payload_only:
        require(args.report_sha is None, "payload-only cannot assert REPORT verification")
        result["anchors_checked"] = ["FINAL.md", "MANIFEST.json"]
    else:
        require(args.report_sha is not None, "explicit detached REPORT anchor required")
        require(digest(root / "REPORT.md") == args.report_sha, "detached REPORT anchor differs")
        anchors = json.loads((root / "ANCHORS.json").read_text())
        require(anchors == {"FINAL.md": args.final_sha, "MANIFEST.json": args.manifest_sha,
                            "REPORT.md": args.report_sha}, "anchor record differs from explicit inputs")
        result["anchors_checked"] = ["FINAL.md", "MANIFEST.json", "REPORT.md"]
    result["artifact_check"] = "passed"
    result["mathematical_grade"] = "none"
    print(json.dumps(result, sort_keys=True))

if __name__ == "__main__":
    main()
