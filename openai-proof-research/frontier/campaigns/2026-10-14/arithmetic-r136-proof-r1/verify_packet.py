#!/usr/bin/env python3
"""Read-only exact-membership verifier for this independently selected packet."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

ENVELOPES = frozenset({"FINAL.md", "MANIFEST.json", "REPORT.md"})


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def safe_relative(value):
    if not isinstance(value, str) or not value or "\\" in value:
        raise ValueError("invalid relative path")
    p = PurePosixPath(value)
    if p.is_absolute() or str(p) != value or any(s in (".", "..") for s in p.parts):
        raise ValueError("unsafe or noncanonical path: " + value)
    return value


def inventory(root, exclude=ENVELOPES):
    if root.is_symlink() or not root.is_dir():
        raise ValueError("root must be an ordinary directory")
    files, directories = {}, {}
    for base, dirs, names in os.walk(root, followlinks=False):
        for name in sorted(dirs + names):
            path = Path(base) / name
            rel = path.relative_to(root).as_posix()
            info = path.lstat()
            if stat.S_ISLNK(info.st_mode):
                raise ValueError("symlink rejected: " + rel)
            mode = format(stat.S_IMODE(info.st_mode), "04o")
            if stat.S_ISDIR(info.st_mode):
                directories[rel] = {"path": rel, "mode": mode}
            elif stat.S_ISREG(info.st_mode):
                if rel not in exclude:
                    files[rel] = {"path": rel, "bytes": info.st_size,
                                  "mode": mode, "sha256": digest(path)}
            else:
                raise ValueError("nonregular entry rejected: " + rel)
    return {"files": [files[k] for k in sorted(files)],
            "directories": [directories[k] for k in sorted(directories)]}


def verify(root, manifest):
    expected = {}
    for kind in ("files", "directories"):
        records = manifest[kind]
        if not isinstance(records, list):
            raise ValueError("invalid inventory list: " + kind)
        by_path = {}
        for row in records:
            path = safe_relative(row["path"])
            if path in by_path or path in ENVELOPES:
                raise ValueError("duplicate or envelope payload: " + path)
            by_path[path] = row
        expected[kind] = by_path
    if set(expected["files"]) & set(expected["directories"]):
        raise ValueError("file/directory path collision")
    observed = inventory(root)
    for kind in ("files", "directories"):
        actual = {r["path"]: r for r in observed[kind]}
        wanted = expected[kind]
        if actual.keys() != wanted.keys():
            missing = sorted(wanted.keys() - actual.keys())
            extra = sorted(actual.keys() - wanted.keys())
            raise ValueError(f"{kind} membership mismatch: missing={missing}, extra={extra}")
        for path in sorted(wanted):
            if actual[path] != wanted[path]:
                raise ValueError("content/size/mode mismatch: " + path)
    return len(observed["files"]), len(observed["directories"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).absolute().parent)
    for name in ("final", "manifest", "report"):
        parser.add_argument("--" + name + "-sha256")
    args = parser.parse_args()
    root = args.root.absolute()
    for name in sorted(ENVELOPES):
        path = root / name
        if path.is_symlink() or not path.is_file():
            raise ValueError("missing or nonregular envelope: " + name)
        anchor = getattr(args, name.split(".")[0].lower() + "_sha256")
        if anchor is not None and digest(path) != anchor:
            raise ValueError("detached envelope anchor mismatch: " + name)
    manifest = json.loads((root / "MANIFEST.json").read_text())
    if manifest.get("schema") != "arithmetic136-proof-r1-selected-packet-v1":
        raise ValueError("unknown manifest schema")
    files, directories = verify(root, manifest)
    print(json.dumps({"verified": True, "payload_files": files,
                      "payload_directories": directories,
                      "detached_anchors_checked": sum(getattr(args, n + "_sha256") is not None
                          for n in ("final", "manifest", "report")),
                      "read_only": True}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print("VERIFICATION FAILED: " + str(exc), file=sys.stderr)
        sys.exit(1)
