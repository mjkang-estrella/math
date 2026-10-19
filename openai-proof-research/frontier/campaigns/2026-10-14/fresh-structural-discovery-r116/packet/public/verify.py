#!/usr/bin/env python3
"""Read-only exact-inventory verifier. Both detached anchors are mandatory.

Trust this code from a separately authenticated copy. A self-contained packet
cannot establish the authenticity of its own verifier or detached anchors.
No mathematical proof or contribution verdict is produced.
"""
import argparse
import hashlib
import json
import re
import stat
from pathlib import Path, PurePosixPath

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def clean_path(value):
    require(isinstance(value, str) and value, "empty/nonstring path")
    p = PurePosixPath(value)
    require(not p.is_absolute() and str(p) == value and
            all(x not in (".", "..") for x in p.parts), "unsafe path")
    return value


def inventory(packet):
    require(not packet.is_symlink() and packet.is_dir(), "invalid packet root")
    files, directories = {}, []
    for p in sorted(packet.rglob("*")):
        rel = p.relative_to(packet).as_posix()
        clean_path(rel)
        info = p.lstat()
        require(not stat.S_ISLNK(info.st_mode), "symlink: " + rel)
        if stat.S_ISDIR(info.st_mode):
            directories.append(rel)
        else:
            require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                    "nonregular or hardlinked file: " + rel)
            data = p.read_bytes()
            files[rel] = {"bytes": len(data), "sha256": sha(data)}
    return files, directories


def verify(packet, expected_manifest, expected_report):
    for h in (expected_manifest, expected_report):
        require(re.fullmatch(r"[0-9a-f]{64}", h) is not None, "bad detached hash")
    files, directories = inventory(packet)
    require("MANIFEST.json" in files, "missing manifest")
    manifest_bytes = (packet / "MANIFEST.json").read_bytes()
    require(sha(manifest_bytes) == expected_manifest, "detached manifest mismatch")
    manifest = json.loads(manifest_bytes)
    require(set(manifest) == {"schema", "pin", "files", "directories"}, "manifest fields")
    require(manifest["schema"] == 1 and manifest["pin"] == PIN, "manifest version/pin")
    for rel in manifest["files"]:
        clean_path(rel)
    require("MANIFEST.json" not in manifest["files"], "self-indexed manifest")
    del files["MANIFEST.json"]
    require(files == manifest["files"], "file inventory/hash mismatch")
    require(directories == manifest["directories"], "directory inventory mismatch")
    require(sha((packet / "public/report.md").read_bytes()) == expected_report,
            "detached report mismatch")
    receipt = json.loads((packet / "private/complete-tree-receipt.json").read_bytes())
    require(receipt["entries"] == 13223 and receipt["truncated"] is False and
            receipt["all_entries_parsed"] is True, "complete-tree receipt")
    require(receipt["sha256"] == "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b",
            "complete-tree identity")
    entries = json.loads((packet / "private/selected-tree-entries.json").read_bytes())
    selected = {e["path"]: e for e in entries}
    require(len(selected) == len(entries), "duplicate selected tree path")
    upstream = json.loads((packet / "private/upstream-receipts.json").read_bytes())
    require(len(upstream) == len(selected), "source receipt count")
    seen = set()
    for r in upstream:
        path = clean_path(r["path"])
        require(path not in seen, "duplicate source receipt")
        seen.add(path)
        require(r["packet_path"] == "private/upstream/" + path, "source layout")
        data = (packet / r["packet_path"]).read_bytes()
        require(len(data) == r["bytes"] and sha(data) == r["sha256"], "source bytes")
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(blob == r["git_blob"] == selected[path]["sha"], "source Git blob")
        require(selected[path]["type"] == "blob", "selected tree type")
        require(r["pinned_raw_url"] == "https://raw.githubusercontent.com/openai/math/" + PIN + "/" + path,
                "source pinned URL")
    primary = json.loads((packet / "private/primary-receipts.json").read_bytes())
    successes = 0
    for r in primary:
        if "error" in r:
            continue
        stem = clean_path(r["stem"])
        require("/" not in stem, "primary stem")
        pdf = (packet / "private/primary" / (stem + ".pdf")).read_bytes()
        txt = (packet / "private/primary" / (stem + ".txt")).read_bytes()
        require(sha(pdf) == r["sha256"] and len(pdf) == r["bytes"], "primary PDF identity")
        require(sha(txt) == r["text_sha256"], "primary extraction identity")
        successes += 1
    return {"integrity": "verified", "mathematical_gate": False,
            "manifest_sha256": expected_manifest, "report_sha256": expected_report,
            "files": len(files), "directories": len(directories),
            "source_files": len(upstream), "primary_successes": successes,
            "complete_tree_replayed": False,
            "scope": "sealed selected entries and full-tree receipt; no network or repository reads"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--expected-manifest", required=True)
    parser.add_argument("--expected-report", required=True)
    args = parser.parse_args()
    try:
        result = verify(args.packet, args.expected_manifest, args.expected_report)
    except (ValueError, OSError, KeyError, TypeError) as exc:
        parser.exit(1, "INTEGRITY REJECTED: " + str(exc) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
