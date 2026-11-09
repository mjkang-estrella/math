#!/usr/bin/env python3
"""Read-only packet authentication. No mathematical verdict; explicit anchors required."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat


def require(condition, message):
    if not condition:
        raise ValueError(message)


def safe(name):
    require(isinstance(name, str) and name and "\\" not in name and "\x00" not in name, "unsafe path")
    p = PurePosixPath(name)
    require(not p.is_absolute() and all(x not in ("", ".", "..") for x in name.split("/")), "unsafe components")
    require(p.as_posix() == name, "noncanonical path")
    return name


def digest(data):
    return hashlib.sha256(data).hexdigest()


def pairs(items):
    out = {}
    for key, value in items:
        require(key not in out, "duplicate JSON key")
        out[key] = value
    return out


def read_json(path):
    return json.loads(path.read_bytes(), object_pairs_hook=pairs)


def bytes_match(data, length, sha):
    require(len(data) == length, "length mismatch")
    require(digest(data) == sha, "SHA256 mismatch")


def controls(root):
    c = root / "private/controls"
    record = read_json(c / "expected.json")
    bytes_match((c / "original.txt").read_bytes(), record["bytes"], record["sha256"])
    bytes_match((c / safe(record["positive"])).read_bytes(), record["bytes"], record["sha256"])
    rejected = False
    try:
        bytes_match((c / safe(record["negative"])).read_bytes(), record["bytes"], record["sha256"])
    except ValueError:
        rejected = True
    require(rejected, "tampered copied control was admitted")
    for name in ("../escape", "/absolute", "a//b", "a/./b", "a/../b", "a\\b"):
        rejected = False
        try:
            safe(name)
        except ValueError:
            rejected = True
        require(rejected, "unsafe control path admitted")


def verify(root, final_sha, manifest_sha, report_sha):
    require(not root.is_symlink() and root.is_dir(), "root must be a real directory")
    anchors = {"private/FINAL.md": final_sha, "MANIFEST.json": manifest_sha, "REPORT.md": report_sha}
    for name, sha in anchors.items():
        require(re.fullmatch(r"[0-9a-f]{64}", sha) is not None, "invalid detached anchor")
        p = root / name
        require(not p.is_symlink() and stat.S_ISREG(p.lstat().st_mode), "unsafe anchor file")
        require(digest(p.read_bytes()) == sha, "detached anchor mismatch: " + name)
    manifest = read_json(root / "MANIFEST.json")
    require(manifest["schema"] == "r162aw-seal-v1", "wrong schema")
    require(manifest["detached"] == ["MANIFEST.json", "REPORT.md"], "wrong detached members")
    rows = manifest["payload"]
    names = [safe(row["path"]) for row in rows]
    require(names == sorted(names) and len(names) == len(set(names)), "payload not sorted and unique")
    require(not set(names).intersection(manifest["detached"]), "detached member in payload")
    expected_files = set(names) | set(manifest["detached"])
    dirs = manifest["directories"]
    dn = [row["path"] for row in dirs]
    require(dn == sorted(dn) and len(dn) == len(set(dn)), "directories not sorted and unique")
    for name in dn:
        if name != ".":
            safe(name)
    found_files, found_dirs = set(), {"."}
    for base, directory_names, file_names in os.walk(root, followlinks=False):
        for name in directory_names + file_names:
            p = Path(base) / name
            rel = p.relative_to(root).as_posix()
            safe(rel)
            st = p.lstat()
            require(not stat.S_ISLNK(st.st_mode), "symlink forbidden: " + rel)
            if stat.S_ISDIR(st.st_mode):
                found_dirs.add(rel)
            else:
                require(stat.S_ISREG(st.st_mode) and st.st_nlink == 1, "nonordinary file: " + rel)
                found_files.add(rel)
    require(found_files == expected_files, "exact file membership mismatch")
    require(found_dirs == set(dn), "exact directory membership mismatch")
    for row in dirs:
        p = root if row["path"] == "." else root / row["path"]
        require(format(stat.S_IMODE(p.lstat().st_mode), "04o") == row["mode"], "directory mode mismatch")
    for row in rows:
        p = root / row["path"]
        require(format(stat.S_IMODE(p.lstat().st_mode), "04o") == row["mode"], "file mode mismatch: " + row["path"])
        bytes_match(p.read_bytes(), row["bytes"], row["sha256"])
    for name in manifest["detached"]:
        require(stat.S_IMODE((root / name).lstat().st_mode) == 0o644, "detached mode mismatch")
    selected = read_json(root / "private/selected-tree.json")
    require(len(selected) == 36, "selected tree entry count")
    selected_paths = [safe(x["path"]) for x in selected]
    require(len(selected_paths) == len(set(selected_paths)), "duplicate selected tree entry")
    blobs = {x["path"]: x for x in selected if x["type"] == "blob"}
    sources = read_json(root / "private/source-authentication.json")
    require(len(sources) == 28 and len({x["path"] for x in sources}) == 28, "canonical count/uniqueness")
    require({x["path"] for x in sources} == set(blobs), "canonical selected membership")
    for row in sources:
        data = (root / "private/source" / safe(row["path"])).read_bytes()
        bytes_match(data, row["size"], row["sha256"])
        git = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\x00" + data).hexdigest()
        require(git == row["git_blob"] == blobs[row["path"]]["sha"], "Git blob mismatch")
        require(len(data) == blobs[row["path"]]["size"], "tree length mismatch")
    contexts = read_json(root / "private/context-bindings.json")
    require(len(contexts) == 5 and len({x["copy"] for x in contexts}) == 5, "context count/uniqueness")
    for row in contexts:
        bytes_match((root / safe(row["copy"])).read_bytes(), row["size"], row["sha256"])
    primary = root / "private/primary"
    primary_count = 0
    for filename in ("access.json", "additional-access.json", "third-access.json"):
        for row in read_json(primary / filename):
            if "error" in row:
                continue
            data = (primary / (safe(row["name"]) + ".pdf")).read_bytes()
            bytes_match(data, row.get("size", row.get("bytes")), row["sha256"])
            primary_count += 1
    for filename, name in (("fourth-access.json", "GT2008v1"), ("fifth-access.json", "GJ2021v2")):
        row = read_json(primary / filename)
        bytes_match((primary / (name + ".pdf")).read_bytes(), row["bytes"], row["sha256"])
        primary_count += 1
    require(primary_count == 10, "primary copy count")
    controls(root)
    print(json.dumps({"artifact_check": "PASS", "payload_files": len(rows), "whole_root_files": len(found_files), "directories_including_root": len(found_dirs), "canonical_blobs": len(sources), "context_copies": len(contexts), "primary_PDFs": primary_count, "copied_controls": "positive accepted; altered copy rejected", "mathematical_gate": "NONE"}, sort_keys=True))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--final-sha256", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--report-sha256", required=True)
    args = parser.parse_args()
    verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256)
