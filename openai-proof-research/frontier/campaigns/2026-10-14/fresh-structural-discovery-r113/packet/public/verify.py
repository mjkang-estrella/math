#!/usr/bin/env python3
"""Read-only packet integrity check. Supply a DETACHED manifest digest.

Trust this verifier/interpreter separately before execution. No mathematical gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    result = {}
    for k, v in pairs:
        require(k not in result, "duplicate JSON key")
        result[k] = v
    return result


def parse(data):
    return json.loads(data, object_pairs_hook=unique_object)


def safe_path(name):
    require(isinstance(name, str) and name and "\\" not in name, "invalid path")
    p = PurePosixPath(name)
    require(not p.is_absolute() and str(p) == name and all(x not in (".", "..") for x in p.parts), "noncanonical path")
    return name


def scan(root):
    require(stat.S_ISDIR(root.lstat().st_mode), "root is not a real directory")
    files, directories = {}, set()
    for here, dirs, names in os.walk(root, followlinks=False):
        for name in dirs + names:
            p = Path(here) / name
            rel = p.relative_to(root).as_posix()
            safe_path(rel)
            info = p.lstat()
            if stat.S_ISDIR(info.st_mode):
                directories.add(rel)
            else:
                require(stat.S_ISREG(info.st_mode), "nonregular file: " + rel)
                require(info.st_nlink == 1, "hard-linked file: " + rel)
                files[rel] = {"path": rel, "bytes": info.st_size, "sha256": digest(p.read_bytes())}
    return files, directories


def verify(root, expected):
    require(re.fullmatch(r"[0-9a-f]{64}", expected) is not None, "detached anchor must be 64 lowercase hex digits")
    files, directories = scan(root)
    require("manifest.json" in files, "missing manifest")
    require(files["manifest.json"]["sha256"] == expected, "detached manifest hash mismatch")
    manifest = parse((root / "manifest.json").read_bytes())
    require(set(manifest) == {"schema", "pin", "directories", "files"}, "manifest schema keys")
    require(manifest["schema"] == "r113-exact-files-v1" and manifest["pin"] == PIN, "manifest schema or pin")
    desired = {}
    for row in manifest["files"]:
        require(set(row) == {"path", "bytes", "sha256"}, "file row keys")
        name = safe_path(row["path"])
        require(name not in desired and name != "manifest.json", "duplicate or recursive manifest member")
        require(type(row["bytes"]) is int and row["bytes"] >= 0, "invalid file size")
        require(re.fullmatch(r"[0-9a-f]{64}", row["sha256"]) is not None, "invalid payload digest")
        desired[name] = row
    require(list(desired) == sorted(desired), "unsorted file inventory")
    ds = manifest["directories"]
    require(ds == sorted(set(ds)) and all(safe_path(x) for x in ds), "invalid directory inventory")
    del files["manifest.json"]
    require(files == desired, "payload membership, size or digest mismatch")
    require(directories == set(ds), "directory membership mismatch")

    def read(name):
        require(name in files, "unlisted receipt: " + name)
        return parse((root / name).read_bytes())

    tree = read("private/context/selected-tree.json")
    require(tree["pin"] == PIN, "tree pin mismatch")
    bypath = {x["path"]: x for x in tree["entries"]}
    require(len(bypath) == len(tree["entries"]), "duplicate selected tree entry")
    upstream = read("private/upstream/receipt.json")
    seen = set()
    for rec in upstream:
        path = safe_path(rec["path"])
        local = safe_path(rec["local"])
        require(path not in seen and path in bypath, "source path mismatch")
        seen.add(path)
        require(local == "private/upstream/" + path and local in files, "source local mismatch")
        data = (root / local).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()
        ent = bypath[path]
        require(ent["type"] == "blob" and blob == ent["sha"] == rec["git_blob"], "Git blob mismatch")
        require(len(data) == ent["size"] == rec["bytes"] and digest(data) == rec["sha256"], "source hash/size mismatch")
        require(rec["raw_url"] == "https://raw.githubusercontent.com/openai/math/" + PIN + "/" + path, "raw pin URL mismatch")
    require(seen == set(bypath), "selected source coverage mismatch")
    require({"private/upstream/" + p for p in seen} == {p for p in files if p.startswith("private/upstream/") and p != "private/upstream/receipt.json"}, "unreceipted source body")
    context = read("private/context/context-receipt.json")
    require(context["pin"] == PIN and context["complete_tree_entries"] == 13223 and context["complete_tree_truncated"] is False, "complete-tree context mismatch")
    ct = [x for x in context["context"] if x["path"] == "sources/preprints-tree.json"]
    require(len(ct) == 1 and ct[0]["sha256"] == tree["complete_tree_sha256"], "complete-tree fingerprint mismatch")
    primary = read("private/primary/receipt.json")
    primary_files = set()
    primary_names = set()
    for rec in primary:
        require(rec["name"] not in primary_names, "duplicate primary receipt")
        primary_names.add(rec["name"])
        if rec["success"] is True:
            for ext, key in ((".pdf", "sha256"), (".txt", "text_sha256")):
                name = safe_path("private/primary/" + rec["name"] + ext)
                require(name in files and files[name]["sha256"] == rec[key], "primary payload mismatch")
                primary_files.add(name)
        else:
            require(rec["success"] is False and bool(rec["error"]), "failed retrieval missing error")
    require(primary_files == {p for p in files if p.startswith("private/primary/") and p != "private/primary/receipt.json"}, "unreceipted primary body")
    for rec in read("private/history/read-receipt.json"):
        name = safe_path(rec["local"])
        require(name in files and files[name]["sha256"] == rec["sha256"], "retained history mismatch")
    return {"status": "integrity_only", "manifest_sha256": expected, "payload_files": len(files), "directories": len(directories), "upstream_blobs": len(upstream), "successful_primary_versions": sum(r["success"] is True for r in primary)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packet", type=Path)
    parser.add_argument("--expected-manifest-sha256", required=True, help="DETACHED final hash; never derive it from this packet")
    args = parser.parse_args()
    try:
        result = verify(args.packet, args.expected_manifest_sha256)
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print("INTEGRITY FAILURE: " + str(exc), file=sys.stderr)
        sys.exit(1)
    print(json.dumps(result, indent=2, sort_keys=True))
