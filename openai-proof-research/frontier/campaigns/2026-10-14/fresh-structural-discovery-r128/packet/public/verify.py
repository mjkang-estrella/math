#!/usr/bin/env python3
"""Read-only r128 evidence verification; no mathematical verdict. MIT."""
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
    return json.loads(read(path))


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
    final = json.loads(final_bytes)
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
    canonical = load(packet / "private/canonical.json")
    require(len(canonical) == 22, "canonical record count")
    for item in canonical:
        record = item["record"]
        require(record == lookup.get(record["path"]), "FULL canonical record mismatch")
        require(record["type"] == "blob", "canonical not blob")
        require(item["url"] == "https://raw.githubusercontent.com/openai/math/" + PIN + "/" + record["path"], "pinned raw URL")
        body = read(packet / safe_path(item["local"]))
        require(len(body) == record["size"] and sha(body) == item["sha256"], "canonical bytes")
        require(hashlib.sha1(b"blob " + str(len(body)).encode() + b"\0" + body).hexdigest() == record["sha"], "Git blob mismatch")
    primary = load(packet / "private/primary/receipts.json")
    require(len(primary) == 6 and sum("error" not in x for x in primary) == 5, "primary counts")
    for item in primary:
        if "error" in item:
            require(item["url"] == "https://arxiv.org/pdf/2306.12576v2" and "404" in item["error"], "failed request record")
            continue
        pdf = read(packet / safe_path(item["local_pdf"]))
        txt = read(packet / safe_path(item["local_text"]))
        require(len(pdf) == item["bytes"] and sha(pdf) == item["pdf_sha256"] and sha(txt) == item["text_sha256"], "primary pair bytes")
        require(item.get("pdftotext_exit", item.get("extraction_exit")) == 0, "primary extraction failure")
    history = load(packet / "private/history/records.json")
    require(len(history) == 36, "history count")
    for item in history:
        body = read(packet / safe_path(item["local"]))
        require(len(body) == item["bytes"] and sha(body) == item["sha256"], "history copy bytes")
        require(read(project / safe_path(item["original"])) == body, "original history binding changed")
    inputs = load(packet / "private/context/input-bindings.json")
    require(len(inputs) == 23, "input count")
    for item in inputs:
        body = read(project / safe_path(item["path"]))
        require(len(body) == item["bytes"] and sha(body) == item["sha256"], "external input binding changed")
    return {"status": "ARTIFACTS_VERIFIED", "packet_payload_files": sum(v["type"] == "file" for v in actual.values()),
            "packet_directories_including_root": sum(v["type"] == "dir" for v in actual.values()),
            "canonical_full_records": 22, "primary_pairs": 5, "failed_requests": 1,
            "history_copies": 36, "external_input_bindings": 23, "mathematical_gate": False}


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
