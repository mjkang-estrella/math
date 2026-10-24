"""Read-only exact-selection verifier. Pass detached anchors explicitly; no trust in ANCHORS.json."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat
RESERVED = {"MANIFEST.json", "REPORT.md", "ANCHORS.json", "CONTROLS.json"}
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def excluded(rel):
    return rel in RESERVED or PurePosixPath(rel).parts[0] == "controls"
def inventory(root):
    files, dirs = [], ["."]
    for current, children, names in os.walk(root, followlinks=False):
        current = Path(current)
        keep = []
        for name in sorted(children):
            p = current / name
            rel = p.relative_to(root).as_posix()
            if p.is_symlink():
                raise ValueError("Symlink: " + rel)
            if not excluded(rel):
                keep.append(name)
                dirs.append(rel)
        children[:] = keep
        for name in sorted(names):
            p = current / name
            rel = p.relative_to(root).as_posix()
            if p.is_symlink():
                raise ValueError("Symlink: " + rel)
            if not excluded(rel):
                if not p.is_file():
                    raise ValueError("Nonregular file: " + rel)
                files.append(rel)
    return sorted(files), sorted(dirs)
def safe(root, rel):
    p = PurePosixPath(rel)
    if p.is_absolute() or ".." in p.parts or p.as_posix() != rel:
        raise ValueError("Unsafe relative path")
    return root / rel

def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root)
    if root.is_symlink():
        raise ValueError("Root symlink")
    for rel, anchor in [("FINAL.md", final_sha), ("MANIFEST.json", manifest_sha), ("REPORT.md", report_sha)]:
        p = safe(root, rel)
        if p.is_symlink() or digest(p) != anchor:
            raise ValueError("Detached anchor mismatch: " + rel)
        if stat.S_IMODE(p.stat().st_mode) != 0o444:
            raise ValueError("Anchor file mode mismatch: " + rel)
    manifest = json.loads((root / "MANIFEST.json").read_text())
    if manifest["schema"] != "r226-exact-packet-v1":
        raise ValueError("Schema mismatch")
    expected = [row["path"] for row in manifest["files"]]
    expected_dirs = [row["path"] for row in manifest["directories"]]
    actual, actual_dirs = inventory(root)
    if expected != sorted(set(expected)) or actual != expected:
        raise ValueError("Exact file selection mismatch")
    if expected_dirs != sorted(set(expected_dirs)) or actual_dirs != expected_dirs:
        raise ValueError("Exact directory selection mismatch")
    for row in manifest["files"]:
        p = safe(root, row["path"])
        if p.stat().st_size != row["bytes"] or digest(p) != row["sha256"]:
            raise ValueError("Content mismatch: " + row["path"])
        if stat.S_IMODE(p.stat().st_mode) != int(row["mode"], 8):
            raise ValueError("Mode mismatch: " + row["path"])
    for row in manifest["directories"]:
        p = safe(root, row["path"])
        if stat.S_IMODE(p.stat().st_mode) != int(row["mode"], 8):
            raise ValueError("Directory mode mismatch: " + row["path"])
    return {"files": len(expected), "directories": len(expected_dirs), "content_and_modes": "matched", "read_only": True, "mathematical_gate": False}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--final-sha256", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--report-sha256", required=True)
    args = parser.parse_args()
    print(json.dumps(verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256), sort_keys=True))
