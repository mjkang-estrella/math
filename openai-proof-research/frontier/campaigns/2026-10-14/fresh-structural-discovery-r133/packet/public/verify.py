#!/usr/bin/env python3
"""Read-only artifact verifier for structural round r133.

Usage:
    python -B packet/public/verify.py --root ROOT --project PROJECT --finalhash DETACHED_SHA256

Checks the detached FINAL anchor, the outside REPORT and packet MANIFEST bound by FINAL, the exact
packet tree, the frozen-statement anchor, the pinned source bodies against the complete preprint
tree, and the primary-file receipts. It writes nothing. This is an artifact check, not a
mathematical verdict.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import sys

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"
TREE_ENTRIES = 13223
FROZEN_SHA256 = "72654d283495baa80aba6349b1b5ebb9a4634ba268d7499a6187ecdd1e311256"
STATUS = "FROZEN_AUTHOR_PROOF_NOMINEE"


class Reject(Exception):
    pass


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def scan(packet: pathlib.Path) -> dict:
    entries = {".": {"type": "dir"}}
    for dirpath, dirnames, filenames in os.walk(packet, followlinks=False):
        d = pathlib.Path(dirpath)
        for name in dirnames + filenames:
            p = d / name
            rel = p.relative_to(packet).as_posix()
            if p.is_symlink():
                raise Reject(f"symlink in packet: {rel}")
            if p.is_dir():
                entries[rel] = {"type": "dir"}
            elif p.is_file():
                if rel == "MANIFEST.json":
                    continue
                entries[rel] = {"type": "file", "bytes": p.stat().st_size, "sha256": sha256(p)}
            else:
                raise Reject(f"special file in packet: {rel}")
    return entries


def verify(root: pathlib.Path, project: pathlib.Path, finalhash: str) -> dict:
    if not re.fullmatch(r"[0-9a-f]{64}", finalhash):
        raise Reject("detached anchor is not a lowercase SHA256")
    final_path = root / "FINAL.json"
    if sha256(final_path) != finalhash:
        raise Reject("detached FINAL mismatch")
    final = json.loads(final_path.read_text())
    expected = {
        "version": 1, "status": STATUS, "frozen": True, "mathematical_gate": False,
        "provider": "Factory Droid", "model": "claude-opus-5-5", "pin": PIN,
        "frozen_statement_sha256": FROZEN_SHA256,
    }
    for k, v in expected.items():
        if final.get(k) != v:
            raise Reject(f"FINAL field {k} unexpected")
    allowed = set(expected) | {"manifest_sha256", "report_sha256", "public_report_sha256", "proof_sha256"}
    if set(final) != allowed:
        raise Reject("FINAL has unexpected or missing fields")
    if sha256(root / "REPORT.md") != final["report_sha256"]:
        raise Reject("outside REPORT mismatch")
    packet = root / "packet"
    manifest_path = packet / "MANIFEST.json"
    if sha256(manifest_path) != final["manifest_sha256"]:
        raise Reject("MANIFEST mismatch")
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("version") != 1:
        raise Reject("MANIFEST version")
    if scan(packet) != manifest["entries"]:
        raise Reject("packet tree differs from MANIFEST")
    ent = manifest["entries"]
    if ent.get("public/frozen-statement.md", {}).get("sha256") != FROZEN_SHA256:
        raise Reject("frozen statement anchor mismatch")
    if ent.get("public/report.md", {}).get("sha256") != final["public_report_sha256"]:
        raise Reject("public report mismatch")
    if ent.get("public/proof.md", {}).get("sha256") != final["proof_sha256"]:
        raise Reject("proof mismatch")

    tree_bytes = (project / "sources/preprints-tree.json").read_bytes()
    if hashlib.sha256(tree_bytes).hexdigest() != TREE_SHA256:
        raise Reject("project preprint tree hash mismatch")
    tree = json.loads(tree_bytes)
    if tree.get("truncated") is not False or len(tree["tree"]) != TREE_ENTRIES:
        raise Reject("project preprint tree incomplete")
    blobs = {e["path"]: e for e in tree["tree"] if e["type"] == "blob"}
    src = packet / "private/source"
    receipts = json.loads((src / "receipts.json").read_text())
    seen = set()
    for r in receipts:
        e = blobs.get(r["path"])
        if e is None:
            raise Reject(f"source path not in tree: {r['path']}")
        if r["url"] != f"https://raw.githubusercontent.com/openai/math/{PIN}/{r['path']}":
            raise Reject(f"source URL not pinned: {r['path']}")
        data = (src / r["path"]).read_bytes()
        if git_blob_sha1(data) != e["sha"] or len(data) != e["size"]:
            raise Reject(f"source body fails tree authentication: {r['path']}")
        if r["git_blob_sha1"] != e["sha"] or r["size"] != e["size"]:
            raise Reject(f"source receipt metadata mismatch: {r['path']}")
        if hashlib.sha256(data).hexdigest() != r["sha256"]:
            raise Reject(f"source receipt SHA256 mismatch: {r['path']}")
        seen.add("private/source/" + r["path"])
    bodies = {k for k, v in ent.items()
              if v["type"] == "file" and k.startswith("private/source/") and k != "private/source/receipts.json"}
    if bodies != seen:
        raise Reject("source bodies and receipts differ")

    prim = packet / "private/primary"
    pr = json.loads((prim / "primary-receipts.json").read_text())
    for r in pr["primary_files"]:
        p = prim / r["file"]
        if p.stat().st_size != r["bytes"] or sha256(p) != r["sha256"]:
            raise Reject(f"primary receipt mismatch: {r['file']}")

    files = sum(1 for v in ent.values() if v["type"] == "file")
    dirs = sum(1 for v in ent.values() if v["type"] == "dir")
    return {
        "status": "ARTIFACTS_VERIFIED", "mathematical_gate": False,
        "packet_payload_files": files, "packet_directories_including_root": dirs,
        "authenticated_source_bodies": len(seen), "primary_receipts": len(pr["primary_files"]),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--project", required=True)
    ap.add_argument("--finalhash", required=True)
    a = ap.parse_args()
    try:
        out = verify(pathlib.Path(a.root), pathlib.Path(a.project), a.finalhash)
    except (Reject, OSError, ValueError, KeyError, TypeError) as exc:
        print(f"REJECT: {exc}")
        sys.exit(1)
    print(json.dumps(out, sort_keys=True))


if __name__ == "__main__":
    main()
