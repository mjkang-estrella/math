#!/usr/bin/env python3
"""Identity verifier only: it does not assess proof, contribution, or acceptance."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
ROOT = Path(__file__).resolve().parent


def fail(message):
    raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_path(name):
    if not isinstance(name, str):
        fail("path is not a string")
    p = PurePosixPath(name)
    if p.is_absolute() or not p.parts or any(x in (".", "..") for x in p.parts):
        fail("unsafe relative path")
    if str(p) != name or "\\" in name:
        fail("noncanonical relative path")
    return ROOT.joinpath(*p.parts)


def anchor(name, expected):
    if re.fullmatch(r"[0-9a-f]{64}", expected) is None:
        fail("invalid external anchor for " + name)
    p = safe_path(name)
    if not p.is_file() or p.is_symlink() or digest(p) != expected:
        fail("external anchor mismatch: " + name)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for label in ("manifest", "proof", "scope", "checkpoint"):
        ap.add_argument("--" + label + "-sha256", required=True)
    args = ap.parse_args()
    anchor("manifest.json", args.manifest_sha256)
    anchor("proof.md", args.proof_sha256)
    anchor("fixed-scope.md", args.scope_sha256)
    anchor("checkpoint.md", args.checkpoint_sha256)

    inventory = json.loads((ROOT / "manifest.json").read_text())
    if set(inventory) != {"schema", "pin", "files", "directories"}:
        fail("unexpected inventory schema")
    if inventory["schema"] != "arithmetic-r18-v1" or inventory["pin"] != PIN:
        fail("wrong schema or pin")
    rows = inventory["files"]
    names = [r["path"] for r in rows]
    if len(set(names)) != len(names) or names != sorted(names):
        fail("duplicate or unsorted inventory files")
    actual_files, actual_dirs = [], []
    for p in ROOT.rglob("*"):
        if p.is_symlink():
            fail("symlink in packet")
        name = p.relative_to(ROOT).as_posix()
        if p.is_dir():
            actual_dirs.append(name)
        elif p.is_file():
            if name != "manifest.json":
                actual_files.append(name)
        else:
            fail("nonregular filesystem object")
    if sorted(actual_files) != names:
        fail("exact file inventory mismatch")
    if sorted(actual_dirs) != inventory["directories"]:
        fail("exact directory inventory mismatch")
    for row in rows:
        if set(row) != {"path", "bytes", "sha256"}:
            fail("unexpected file record fields")
        p = safe_path(row["path"])
        if p.stat().st_size != row["bytes"] or digest(p) != row["sha256"]:
            fail("file identity mismatch: " + row["path"])

    tree_path = ROOT / "private/context/sources/preprints-tree.json"
    tree = json.loads(tree_path.read_text())
    if tree.get("truncated") is not False:
        fail("source tree is not complete")
    blobs = {e["path"]: e["sha"] for e in tree["tree"] if e["type"] == "blob"}
    source_receipts = json.loads((ROOT / "receipts.json").read_text())
    seen_sources = set()
    for row in source_receipts:
        if row["upstream_path"] in seen_sources:
            fail("duplicate source receipt")
        seen_sources.add(row["upstream_path"])
        expected_url = "https://raw.githubusercontent.com/openai/math/" + PIN + "/" + row["upstream_path"]
        if row["url"] != expected_url:
            fail("unpinned source URL")
        p = safe_path(row["path"])
        b = p.read_bytes()
        git_sha = hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
        if git_sha != row["git_blob_sha1"] or git_sha != blobs.get(row["upstream_path"]):
            fail("source Git identity mismatch")
        if digest(p) != row["sha256"]:
            fail("source SHA256 mismatch")
    expected_sources = {
        p for p in blobs
        if p.startswith("preprints/The-Generalized-Mukai-Conjecture-September-24-2026/")
        and p.endswith((".tex", ".bib", ".md"))
    }
    if seen_sources != expected_sources:
        fail("incomplete family063 text inventory")

    primaries = json.loads((ROOT / "primary-receipts.json").read_text())
    seen_primary = set()
    for row in primaries:
        if row["pdf"] in seen_primary or not row["url"].startswith("https://"):
            fail("invalid primary receipt")
        seen_primary.add(row["pdf"])
        pdf, txt = safe_path(row["pdf"]), safe_path(row["text"])
        if not pdf.read_bytes().startswith(b"%PDF-"):
            fail("primary body is not a PDF")
        if digest(pdf) != row["sha256"] or digest(txt) != row["text_sha256"]:
            fail("primary receipt identity mismatch")

    prior = {
        "r16-checkpoint.md": "026a5d63d21ca5c140d90c6a150199e1dbfefb28166371e4c19f62ee05cff09c",
        "r17-checkpoint.md": "a7e13d88ecec3b1645fc9afd7cffae13a20af024e84010020f7e1516962db024",
    }
    for name, expected in prior.items():
        if digest(ROOT / "private/context" / name) != expected:
            fail("prior checkpoint differs from parent-supplied anchor")
    context_files = sum(p.is_file() for p in (ROOT / "private/context").rglob("*"))
    print(json.dumps({
        "status": "IDENTITY_PASS_ONLY", "files": len(rows),
        "directories": len(actual_dirs), "pinned_source_blobs": len(source_receipts),
        "primary_pdfs": len(primaries), "context_snapshots": context_files,
        "mathematical_verdict": "not assessed", "acceptance": "not claimed",
    }, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print("VERIFY_FAIL: " + str(exc), file=sys.stderr)
        sys.exit(1)
