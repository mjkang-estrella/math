#!/usr/bin/env python3
"""Read-only artifact verifier for structural round r135.

Usage:
    python3 -B packet/public/verify.py --root ROOT --project PROJECT --finalhash DETACHED_SHA256

Checks the detached FINAL anchor, the outside REPORT and packet MANIFEST bound by FINAL, the exact
packet tree, the frozen-statement anchor, pinned source bodies against the complete preprint tree,
and primary receipts. It writes nothing. This is an artifact check, not a mathematical verdict.
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
FROZEN_SHA256 = "1000a115e013b3bc28247fdc03f33b8d4ae3ee8ee2a41ce4da55c79e1081a99d"
STATUS = "FROZEN_AUTHOR_PROOF_NOMINEE"


class Reject(Exception):
    pass


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob_sha1(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def scan(packet):
    entries = {".": {"type": "dir"}}
    for dirpath, dirnames, filenames in os.walk(packet, followlinks=False):
        d = pathlib.Path(dirpath)
        for name in dirnames + filenames:
            p = d / name
            rel = p.relative_to(packet).as_posix()
            if p.is_symlink():
                raise Reject("symlink in packet: " + rel)
            if p.is_dir():
                entries[rel] = {"type": "dir"}
            elif p.is_file():
                if rel == "MANIFEST.json":
                    continue
                entries[rel] = {"type": "file", "bytes": p.stat().st_size, "sha256": sha256(p)}
            else:
                raise Reject("special file in packet: " + rel)
    return entries


def verify(root, project, finalhash):
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
            raise Reject("FINAL field %s unexpected" % k)
    allowed = set(expected) | {"manifest_sha256", "report_sha256", "public_report_sha256",
                               "proof_sha256"}
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
    ent = manifest["entries"]
    if scan(packet) != ent:
        raise Reject("packet tree differs from MANIFEST")
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
    items = tree["tree"] if isinstance(tree, dict) else tree
    if len(items) != TREE_ENTRIES:
        raise Reject("project preprint tree incomplete")
    blobs = {e["path"]: e for e in items if e["type"] == "blob"}
    src = packet / "private/source"
    receipts = json.loads((src / "receipts.json").read_text())
    if not isinstance(receipts, list):
        raise Reject("source receipts not a list")
    seen = set()
    for r in receipts:
        path = r["path"]
        e = blobs.get(path)
        if e is None:
            raise Reject("source path not in tree: " + path)
        if r["url"] != "https://raw.githubusercontent.com/openai/math/%s/%s" % (PIN, path):
            raise Reject("source URL not pinned: " + path)
        if not r.get("authenticated"):
            raise Reject("source receipt not authenticated: " + path)
        data = (src / path.replace("/", "__")).read_bytes()
        if git_blob_sha1(data) != e["sha"] or len(data) != e["size"]:
            raise Reject("source body fails tree authentication: " + path)
        if r["git_blob_sha1"] != e["sha"] or r["size"] != e["size"]:
            raise Reject("source receipt metadata mismatch: " + path)
        if hashlib.sha256(data).hexdigest() != r["sha256"]:
            raise Reject("source receipt SHA256 mismatch: " + path)
        seen.add("private/source/" + path.replace("/", "__"))
    bodies = {k for k, v in ent.items() if k.startswith("private/source/") and v["type"] == "file"
              and k != "private/source/receipts.json"}
    if bodies != seen:
        raise Reject("unreceipted or missing source bodies")

    prim = packet / "private/primary"
    precs = json.loads((prim / "receipts.json").read_text())
    pfiles = {k for k, v in ent.items() if k.startswith("private/primary/") and v["type"] == "file"
              and k != "private/primary/receipts.json"}
    covered = set()
    for name, r in precs.items():
        if sha256(prim / name) != r["sha256"] or (prim / name).stat().st_size != r["bytes"]:
            raise Reject("primary receipt mismatch: " + name)
        if sha256(prim / r["text"]) != r["text_sha256"]:
            raise Reject("primary text receipt mismatch: " + name)
        covered |= {"private/primary/" + name, "private/primary/" + r["text"]}
    if covered != pfiles:
        raise Reject("unreceipted or missing primary files")
    return {
        "status": "ARTIFACTS_VERIFIED", "mathematical_gate": False,
        "authenticated_source_bodies": len(seen), "primary_receipts": len(precs),
        "packet_payload_files": sum(1 for v in ent.values() if v["type"] == "file"),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--project", required=True)
    ap.add_argument("--finalhash", required=True)
    a = ap.parse_args()
    try:
        out = verify(pathlib.Path(a.root), pathlib.Path(a.project), a.finalhash)
    except (Reject, OSError, ValueError, KeyError) as exc:
        print("REJECT:", exc)
        return 1
    print(json.dumps(out, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
