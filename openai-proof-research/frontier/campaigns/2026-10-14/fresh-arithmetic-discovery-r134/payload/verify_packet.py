"""Read-only packet verification with three mandatory detached SHA256 anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path

def sha(data):
    return hashlib.sha256(data).hexdigest()

def inventory(root):
    files, dirs = set(), set()
    for current, subdirs, names in os.walk(root, followlinks=False):
        base = Path(current)
        for name in subdirs:
            p = base / name
            if p.is_symlink():
                raise ValueError("symlink directory: " + str(p))
            dirs.add(p.relative_to(root).as_posix())
        for name in names:
            p = base / name
            if p.is_symlink() or not p.is_file():
                raise ValueError("nonregular file: " + str(p))
            files.add(p.relative_to(root).as_posix())
    return files, dirs

def check_entries(base, entries):
    for item in entries:
        p = Path(item["path"])
        if p.is_absolute() or ".." in p.parts or p.as_posix() != item["path"]:
            raise ValueError("unsafe relative path")
        f = base / p
        if f.is_symlink() or not f.is_file():
            raise ValueError("missing or nonregular: " + item["path"])
        b = f.read_bytes()
        if len(b) != item["bytes"] or sha(b) != item["sha256"]:
            raise ValueError("content mismatch: " + item["path"])

def copied_control(base):
    c = json.loads((base / "CONTROL.json").read_bytes())
    fs, ds = inventory(base)
    if ds or fs != {"CONTROL.json"} | {e["path"] for e in c["files"]}:
        raise ValueError("control membership mismatch")
    check_entries(base, c["files"])

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("root", type=Path)
    ap.add_argument("--final-sha256", required=True)
    ap.add_argument("--manifest-sha256", required=True)
    ap.add_argument("--report-sha256", required=True)
    args = ap.parse_args()
    root = args.root.resolve(strict=True)
    anchors = {"FINAL.md": args.final_sha256, "MANIFEST.json": args.manifest_sha256,
               "REPORT.md": args.report_sha256}
    for name, digest in anchors.items():
        if len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
            raise ValueError("invalid detached anchor")
        if sha((root / name).read_bytes()) != digest:
            raise ValueError("detached anchor mismatch: " + name)
    m = json.loads((root / "MANIFEST.json").read_bytes())
    fs, ds = inventory(root)
    if fs != set(anchors) | {e["path"] for e in m["files"]}:
        raise ValueError("packet file membership mismatch")
    if ds != set(m["directories"]):
        raise ValueError("packet directory membership mismatch")
    check_entries(root, m["files"])
    copied_control(root / "payload/controls/clean")
    try:
        copied_control(root / "payload/controls/altered")
    except ValueError as exc:
        if str(exc) != "content mismatch: selection.md":
            raise
    else:
        raise ValueError("altered copied control unexpectedly accepted")
    print(json.dumps({"packet_files": len(m["files"]), "detached_anchors": "matched",
                      "membership_and_bytes": "matched",
                      "clean_copied_control": "accepted",
                      "altered_copied_control": "rejected as expected",
                      "mathematical_gate": False}, indent=2))

if __name__ == "__main__":
    main()
