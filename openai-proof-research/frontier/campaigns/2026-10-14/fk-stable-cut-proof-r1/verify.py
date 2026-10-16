#!/usr/bin/env python3
"""Read-only audit-package authentication. Original code MIT.

Usage: python -B verify.py --seal-sha256 EXTERNAL_SHA256
Does not execute any inventoried checker or write caches/receipts.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def validate(p, entry):
    require(p.is_file() and not p.is_symlink(), "not a regular file: " + str(p))
    require(p.stat().st_size == entry["size"], "size: " + str(p))
    require(sha(p) == entry["sha256"], "SHA256: " + str(p))


def relative(root, name):
    p = PurePosixPath(name)
    require(not p.is_absolute() and ".." not in p.parts, "unsafe relative path")
    return root.joinpath(*p.parts)


def membership(root):
    out = set()
    for p in root.rglob("*"):
        require(not p.is_symlink(), "symlink: " + str(p))
        if p.is_file():
            out.add(p.relative_to(root).as_posix())
    return out


ap = argparse.ArgumentParser()
ap.add_argument("--seal-sha256", required=True)
args = ap.parse_args()
root = Path(__file__).resolve().parent
require(sha(root/"seal.json") == args.seal_sha256, "external seal anchor")
require((root/"seal.sha256").read_text() == args.seal_sha256+"  seal.json\n",
        "detached seal text")
seal = json.loads((root/"seal.json").read_text())
for key in ("inputs", "outputs"):
    validate(relative(root, seal[key]["path"]), seal[key])
inputs = json.loads((root/seal["inputs"]["path"]).read_text())
outputs = json.loads((root/seal["outputs"]["path"]).read_text())
candidate = Path(inputs["read_only_root"])
input_names = [e["path"] for e in inputs["files"]]
output_names = [e["path"] for e in outputs["files"]]
require(len(set(input_names)) == len(input_names), "duplicate input paths")
require(len(set(output_names)) == len(output_names), "duplicate output paths")
for e in inputs["files"]:
    validate(relative(candidate,e["path"]), e)
for e in inputs["external_files"]:
    p = Path(e["path"])
    require(p.is_absolute(), "external input must be absolute")
    validate(p,e)
for e in outputs["files"]:
    validate(relative(root,e["path"]), e)
require(membership(candidate) == set(input_names), "candidate membership")
metadata = {"inputs-manifest.json", "outputs-manifest.json", "seal.json", "seal.sha256"}
require(membership(root) == set(output_names)|metadata, "review membership")
print(json.dumps({"status":"PASS_HASH_ONLY",
                  "candidate_files":len(input_names),
                  "external_input_files":len(inputs["external_files"]),
                  "review_payload_files":len(output_names),
                  "checkers_executed":False,
                  "files_written":False}, sort_keys=True))
