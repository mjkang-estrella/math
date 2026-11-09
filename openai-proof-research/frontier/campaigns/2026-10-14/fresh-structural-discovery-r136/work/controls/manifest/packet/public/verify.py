#!/usr/bin/env python3
"""Read-only artifact verification. Supply all three detached anchors explicitly.
This script does not assess mathematical correctness, contribution or acceptance.
Run with python -B; no network, subprocesses, imports of local code or file writes.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"
REGISTERS = ("originals-before.json", "history-inputs-before.json",
             "thin-history-inputs-before.json", "additional-inputs-before.json")
MUTABLE = "frontier/NEW-TEN-2026-10-14.md"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def relative(text):
    p = PurePosixPath(text)
    require(not p.is_absolute() and str(p) == text and ".." not in p.parts,
            "unsafe relative path")
    return Path(text)


def regular(path):
    s = path.lstat()
    require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1,
            "non-regular, symbolic or multiply linked file: " + str(path))
    return path.read_bytes()


def anchored(path, expected):
    require(len(expected) == 64 and all(c in "0123456789abcdef" for c in expected),
            "anchor must be full lowercase SHA256")
    data = regular(path)
    require(digest(data) == expected, "detached anchor mismatch: " + str(path))
    require(stat.S_IMODE(path.lstat().st_mode) == 0o644, "anchor file mode")
    return data


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", required=True, type=Path)
    ap.add_argument("--project", required=True, type=Path)
    for label in ("final", "manifest", "report"):
        ap.add_argument("--" + label + "-sha256", required=True)
    args = ap.parse_args()
    root, project = args.root.absolute(), args.project.absolute()
    packet = root / "packet"
    final = json.loads(anchored(root / "FINAL.json", args.final_sha256))
    manifest = json.loads(anchored(packet / "MANIFEST.json", args.manifest_sha256))
    anchored(root / "REPORT.md", args.report_sha256)
    require(final["manifest_sha256"] == args.manifest_sha256 and
            final["report_sha256"] == args.report_sha256, "FINAL bindings")
    require(final["status"] == "PREFREEZE/no nominee" and
            final["scope_frozen"] is False, "outcome metadata")
    require(not packet.is_symlink() and packet.is_dir(), "packet root type")
    actual_files, actual_dirs = {}, {".": stat.S_IMODE(packet.stat().st_mode)}
    for base, dirs, files in os.walk(packet, followlinks=False):
        for name in dirs:
            p = Path(base) / name
            st = p.lstat()
            require(stat.S_ISDIR(st.st_mode), "non-directory inventory entry")
            actual_dirs[p.relative_to(packet).as_posix()] = stat.S_IMODE(st.st_mode)
        for name in files:
            p = Path(base) / name
            rel = p.relative_to(packet).as_posix()
            data = regular(p)
            if rel != "MANIFEST.json":
                actual_files[rel] = {"bytes": len(data), "sha256": digest(data),
                                     "mode": stat.S_IMODE(p.lstat().st_mode)}
    require(actual_files == manifest["files"], "packet inventory/content/mode mismatch")
    require(actual_dirs == manifest["directories"], "packet directory inventory/mode mismatch")
    private = packet / "private"
    tree_data = regular(private / "inputs/03-preprints-tree.json")
    require(digest(tree_data) == TREE_SHA256, "complete tree digest")
    tree = json.loads(tree_data)
    require(tree["truncated"] is False and len(tree["tree"]) == 13223,
            "complete tree extent")
    entries = {e["path"]: e for e in tree["tree"]}
    sources = json.loads(regular(private / "source-authentication.json"))
    require(len({e["local"] for e in sources}) == len(sources), "source local-path collision")
    for e in sources:
        data = regular(root / relative(e["local"]))
        t = entries[e["path"]]
        require(len(data) == e["size"] == t["size"] and digest(data) == e["sha256"],
                "source size/SHA256: " + e["path"])
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(blob == e["sha"] == t["sha"], "source Git blob: " + e["path"])
        require(e["url_raw"] == "https://raw.githubusercontent.com/openai/math/" + PIN + "/" + e["path"],
                "source pinned URL")
    primaries = json.loads(regular(private / "primary-authentication.json"))
    for e in primaries:
        name = relative(e["name"])
        pdf = regular(private / "primary" / (str(name) + ".pdf"))
        txt = regular(private / "primary" / (str(name) + ".txt"))
        require(len(pdf) == e["bytes"] and digest(pdf) == e["sha256"] and
                digest(txt) == e["text_sha256"], "primary authentication")
    stable = 0
    for name in REGISTERS:
        register = json.loads(regular(private / name))
        for e in register["files"] if isinstance(register, dict) else register:
            copied = regular(root / relative(e["copy"]))
            require(digest(copied) == e["sha256"] and len(copied) == e["bytes"],
                    "input copy binding")
            if e["path"] == MUTABLE:
                continue
            require(not any(p in e["path"].split("/") for p in
                            ("fresh-arithmetic-discovery-r101", "t088p133-proof-r3")),
                    "active original prohibited")
            original = regular(project / relative(e["path"]))
            require(digest(original) == e["sha256"] and len(original) == e["bytes"],
                    "stable original changed: " + e["path"])
            stable += 1
    require(stable == 29, "stable original count")
    print(json.dumps({"artifact_integrity": "verified", "payload_files": len(actual_files),
                      "authenticated_source_blobs": len(sources), "primary_versions": len(primaries),
                      "stable_originals_unchanged": stable,
                      "mutable_ledger": "excluded from live immutability requirement",
                      "mathematical_gate": "none"}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print("VERIFICATION FAILED: " + str(exc), file=sys.stderr)
        sys.exit(1)
