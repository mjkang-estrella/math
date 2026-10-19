#!/usr/bin/env python3
"""Read-only r130 evidence verification; no mathematical verdict. MIT."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

sys.dont_write_bytecode = True
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
TREE_SHA = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"
COUNTS = {"canonical": 8, "history": 15, "inputs": 4, "removed": 10, "search": 3}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def install_audit():
    def audit(event, args):
        if event == "open":
            mode, flags = args[1], args[2]
            if (isinstance(mode, str) and any(c in mode for c in "wax+")) or (
                isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)
            ):
                raise PermissionError("readonly verifier denied write")
        if event.startswith(("socket.", "subprocess.", "os.exec", "os.spawn")) or event in {
            "os.system", "os.remove", "os.rename", "os.mkdir", "os.rmdir", "os.chmod",
            "os.chown", "os.link", "os.symlink", "os.truncate", "os.utime", "shutil.copyfile",
        }:
            raise PermissionError("readonly verifier denied " + event)
    sys.addaudithook(audit)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def regular(path):
    s = path.lstat()
    require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, "not single-link regular file: " + str(path))
    return s


def read(path):
    regular(path)
    return path.read_bytes()


def load(path):
    return json.loads(read(path), object_pairs_hook=no_duplicates)


def no_duplicates(pairs):
    keys = [k for k, _ in pairs]
    require(len(keys) == len(set(keys)), "duplicate JSON key")
    return dict(pairs)


def safe_path(name):
    require(isinstance(name, str), "non-string path")
    p = PurePosixPath(name)
    require(name and not p.is_absolute() and ".." not in p.parts and str(p) == name and "\\" not in name,
            "unsafe/noncanonical path")
    return name


def inventory(root, omit_manifest=False):
    require(stat.S_ISDIR(root.lstat().st_mode), "root is not a real directory")
    rows = {".": {"type": "dir", "mode": stat.S_IMODE(root.lstat().st_mode)}}

    def walk(directory):
        for p in sorted(directory.iterdir()):
            name = p.relative_to(root).as_posix()
            if omit_manifest and name == "MANIFEST.json":
                continue
            safe_path(name)
            s = p.lstat()
            if stat.S_ISDIR(s.st_mode):
                rows[name] = {"type": "dir", "mode": stat.S_IMODE(s.st_mode)}
                walk(p)
            else:
                regular(p)
                rows[name] = {"type": "file", "mode": stat.S_IMODE(s.st_mode), "bytes": s.st_size,
                              "sha256": sha(p.read_bytes()), "nlink": s.st_nlink}
    walk(root)
    return rows


def verify(root, project, finalhash):
    require(re.fullmatch(r"[0-9a-f]{64}", finalhash) is not None, "a detached final hash is required")
    require(stat.S_ISDIR(root.lstat().st_mode), "root link/type")
    allowed = {"packet", "REPORT.md", "FINAL.json", "FINAL.sha256", "REPORT.sha256", "artifact-controls.json"}
    require({p.name for p in root.iterdir()} <= allowed, "unexpected outside-packet item")
    for p in root.iterdir():
        if p.name != "packet":
            regular(p)
    final_bytes = read(root / "FINAL.json")
    require(sha(final_bytes) == finalhash, "detached FINAL mismatch")
    final = json.loads(final_bytes, object_pairs_hook=no_duplicates)
    require(final["status"] == "PREFREEZE_NO_NOMINEE" and final["frozen"] is False, "status mismatch")
    require(final["mathematical_gate"] is False and final["pin"] == PIN, "gate/pin mismatch")
    packet = root / "packet"
    require(sha(read(packet / "MANIFEST.json")) == final["manifest_sha256"], "manifest anchor mismatch")
    manifest = load(packet / "MANIFEST.json")
    require(manifest["version"] == 1, "manifest version")
    for name in manifest["entries"]:
        if name != ".":
            safe_path(name)
    actual = inventory(packet, True)
    require(actual == manifest["entries"], "exact packet inventory mismatch")
    require(sha(read(root / "REPORT.md")) == final["report_sha256"], "outside report mismatch")
    require(sha(read(packet / "public/report.md")) == final["public_report_sha256"], "public report mismatch")
    for name, expected in [("FINAL.sha256", finalhash), ("REPORT.sha256", final["report_sha256"])]:
        if (root / name).exists():
            require(read(root / name).decode() == expected + "\n", "convenience hash mismatch")
    tree_bytes = read(project / "sources/preprints-tree.json")
    require(sha(tree_bytes) == TREE_SHA, "external complete tree anchor")
    tree = json.loads(tree_bytes)
    require(tree["truncated"] is False and len(tree["tree"]) == 13223, "complete tree shape")
    lookup = {x["path"]: x for x in tree["tree"]}
    require(len(lookup) == 13223, "duplicate canonical path")
    check = load(packet / "private/context/tree-check.json")
    require(check["sha256"] == TREE_SHA and check["entries"] == 13223 and check["pinned_commit"] == PIN
            and check["truncated"] is False, "tree-check record")
    canonical = load(packet / "private/canonical.json")
    require(len(canonical) == COUNTS["canonical"], "canonical record count")
    locals_seen = set()
    for item in canonical:
        record = item["record"]
        require(record == lookup.get(record["path"]), "FULL canonical record mismatch")
        require(record["type"] == "blob", "canonical not blob")
        require(item["url"] == "https://raw.githubusercontent.com/openai/math/" + PIN + "/" + record["path"], "pinned raw URL")
        require(item["local"] == "private/source/" + record["path"], "canonical local path")
        body = read(packet / safe_path(item["local"]))
        require(len(body) == record["size"] and sha(body) == item["sha256"], "canonical bytes")
        require(hashlib.sha1(b"blob " + str(len(body)).encode() + b"\0" + body).hexdigest() == record["sha"], "Git blob mismatch")
        locals_seen.add(item["local"])
    source_files = {n for n, v in actual.items() if v["type"] == "file" and n.startswith("private/source/")}
    require(source_files == locals_seen, "uncatalogued source body")
    removed = load(packet / "private/context/removed-acquisitions.json")
    require(len(removed) == COUNTS["removed"], "removed acquisition count")
    for item in removed:
        record = lookup.get(item["path"])
        require(record is not None and record["size"] == item["bytes"], "removed acquisition record")
        require(not (packet / "private/source" / safe_path(item["path"])).exists(), "removed body present")
    history = load(packet / "private/history/records.json")
    require(len(history) == COUNTS["history"], "history count")
    for item in history:
        body = read(packet / safe_path(item["local"]))
        require(len(body) == item["bytes"] and sha(body) == item["sha256"], "history copy bytes")
        require(read(project / safe_path(item["original"])) == body, "original history binding changed")
    inputs = load(packet / "private/context/input-bindings.json")
    require(len(inputs) == COUNTS["inputs"], "input count")
    for item in inputs:
        body = read(project / safe_path(item["path"]))
        require(len(body) == item["bytes"] and sha(body) == item["sha256"], "external input binding changed")
    searches = sorted(n for n in actual if n.startswith("private/search/") and actual[n]["type"] == "file")
    require(len(searches) == COUNTS["search"], "search receipt count")
    return {"status": "ARTIFACTS_VERIFIED", "packet_payload_files": sum(v["type"] == "file" for v in actual.values()),
            "packet_directories_including_root": sum(v["type"] == "dir" for v in actual.values()),
            "canonical_full_records": COUNTS["canonical"], "removed_acquisitions": COUNTS["removed"],
            "history_copies": COUNTS["history"], "external_input_bindings": COUNTS["inputs"],
            "search_receipts": COUNTS["search"], "mathematical_gate": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--finalhash", required=True, help="Detached SHA256 of FINAL.json, supplied independently")
    args = parser.parse_args()
    install_audit()
    try:
        print(json.dumps(verify(args.root.absolute(), args.project.absolute(), args.finalhash), sort_keys=True))
    except Exception as exc:
        print("REJECT: " + str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
