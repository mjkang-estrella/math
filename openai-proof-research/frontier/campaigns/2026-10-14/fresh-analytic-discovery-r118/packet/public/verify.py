#!/usr/bin/env python3
"""Read-only r118 byte/provenance verifier. This is not a mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
TREE_HASH = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def regular(path):
    s = path.lstat()
    require(stat.S_ISREG(s.st_mode), "non-regular or symlink file: " + str(path))
    require(s.st_nlink == 1, "hard-linked file: " + str(path))
    return path.read_bytes()

def unique_object(pairs):
    d = {}
    for k, v in pairs:
        require(k not in d, "duplicate JSON key: " + k)
        d[k] = v
    return d

def decode(data):
    return json.loads(data, object_pairs_hook=unique_object)

def relative(name):
    require(isinstance(name, str) and name, "invalid relative path")
    p = PurePosixPath(name)
    require(not p.is_absolute() and str(p) == name and ".." not in p.parts,
            "unsafe or noncanonical relative path: " + name)
    require("\\" not in name, "backslash in relative path")
    return name

def inventory(packet):
    require(stat.S_ISDIR(packet.lstat().st_mode), "packet is not a real directory")
    files, dirs = {}, []
    for parent, names, leaves in os.walk(packet, followlinks=False):
        for name in sorted(names):
            p = Path(parent) / name
            require(stat.S_ISDIR(p.lstat().st_mode), "non-directory or symlink directory: " + str(p))
            dirs.append(p.relative_to(packet).as_posix())
        for name in sorted(leaves):
            p = Path(parent) / name
            b = regular(p)
            files[p.relative_to(packet).as_posix()] = {"bytes": len(b), "sha256": sha(b)}
    return dict(sorted(files.items())), sorted(dirs)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", required=True)
    ap.add_argument("--tree", required=True)
    ap.add_argument("--finalhash", required=True, help="DETACHED trusted SHA256 of FINAL.json")
    ap.add_argument("--reporthash", required=True, help="DETACHED trusted SHA256 of public/report.md")
    args = ap.parse_args()
    for name in ["finalhash", "reporthash"]:
        require(re.fullmatch(r"[0-9a-f]{64}", getattr(args, name)) is not None,
                "invalid detached " + name)
    root = Path(args.root).absolute()
    require(stat.S_ISDIR(root.lstat().st_mode), "root is not a real directory")
    final_bytes = regular(root / "FINAL.json")
    require(sha(final_bytes) == args.finalhash, "detached finalhash mismatch")
    final = decode(final_bytes)
    require(set(final) == {"format", "pin", "tree_sha256", "manifest_sha256", "report_sha256"},
            "unexpected FINAL schema")
    require(final["format"] == "r118-prefreeze-v1" and final["pin"] == PIN, "wrong final format or pin")
    require(final["report_sha256"] == args.reporthash, "detached reporthash mismatch")
    require(final["tree_sha256"] == TREE_HASH, "wrong bound complete tree")
    mb = regular(root / "MANIFEST.json")
    require(sha(mb) == final["manifest_sha256"], "manifest hash mismatch")
    m = decode(mb)
    require(set(m) == {"format", "files", "directories"} and m["format"] == "r118-exact-packet-v1",
            "unexpected manifest schema")
    expected = {}
    for item in m["files"]:
        require(set(item) == {"path", "bytes", "sha256"}, "unexpected manifest file schema")
        name = relative(item["path"])
        require(name not in expected, "duplicate manifest file")
        require(type(item["bytes"]) is int and item["bytes"] >= 0, "invalid manifest size")
        require(re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) is not None, "invalid manifest hash")
        expected[name] = {"bytes": item["bytes"], "sha256": item["sha256"]}
    require(list(expected) == sorted(expected), "manifest files not lexically sorted")
    dirs = [relative(d) for d in m["directories"]]
    require(dirs == sorted(set(dirs)), "manifest directories not unique/sorted")
    packet = root / "packet"
    actual, actual_dirs = inventory(packet)
    require(set(actual) == set(expected), "packet file membership mismatch")
    require(actual_dirs == dirs, "packet directory membership mismatch")
    require(actual == expected, "packet file bytes/hash mismatch")
    require(actual["public/report.md"]["sha256"] == args.reporthash, "report bytes mismatch")
    tb = regular(Path(args.tree))
    require(sha(tb) == TREE_HASH, "external complete tree hash mismatch")
    tree = decode(tb)
    require(tree.get("truncated") is False and len(tree["tree"]) == 13223, "incomplete tree")
    entries = tree["tree"]
    require(sum(x["type"] == "blob" for x in entries) == 10373 and
            sum(x["type"] == "tree" for x in entries) == 2850, "wrong complete tree inventory")
    bypath = {x["path"]: x for x in entries}
    require(len(bypath) == len(entries), "duplicate canonical tree path")
    sources = decode(regular(packet / "public/source-register.json"))
    source_files = set()
    for s in sources:
        path, file = relative(s["path"]), relative(s["file"])
        require(file == "private/upstream/" + path and file not in source_files, "source location/duplicate mismatch")
        source_files.add(file)
        require(s["url"] == "https://raw.githubusercontent.com/openai/math/" + PIN + "/" + path,
                "source URL not canonical pinned raw URL")
        e = bypath.get(path)
        require(e and e["type"] == "blob" and e["sha"] == s["git_blob"], "source canonical Git tree mismatch")
        b = regular(packet / file)
        git_blob = hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
        require(git_blob == s["git_blob"] and sha(b) == s["sha256"] and len(b) == s["bytes"],
                "source identity mismatch")
    require(source_files == {x for x in actual if x.startswith("private/upstream/")}, "source register membership mismatch")
    primaries = decode(regular(packet / "public/primary-register.json"))
    primary_files = set()
    for s in primaries:
        require(s["status"] == "acquired", "unexpected primary status")
        for kind in ["pdf", "text"]:
            file = relative(s[kind])
            require(file.startswith("private/primary/") and file not in primary_files, "primary location/duplicate mismatch")
            primary_files.add(file)
            require(sha(regular(packet / file)) == s[kind + "_sha256"], "primary identity mismatch")
    require(primary_files == {x for x in actual if x.startswith("private/primary/")}, "primary register membership mismatch")
    print(json.dumps({"status": "INTEGRITY_OK_ONLY", "files": len(actual), "directories": len(dirs),
                      "canonical_sources": len(sources), "primary_pairs": len(primaries),
                      "finalhash": args.finalhash, "reporthash": args.reporthash}, sort_keys=True))

if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as error:
        print("INTEGRITY_REJECT: " + str(error), file=sys.stderr)
        sys.exit(1)
