#!/usr/bin/env python3
"""Seal the review root: write packet/MANIFEST.json, then FINAL.json.

Usage:
  python -B seal.py manifest --root REVIEW_ROOT
  python -B seal.py final --root REVIEW_ROOT --author-finalhash DETACHED_AUTHOR_FINAL_SHA256

Run "manifest" after every packet file is final, write REPORT.md (which quotes
the manifest hash), then run "final". The FINAL hash is reported detached.
"""
import argparse
import hashlib
import json
import os
import sys

sys.dont_write_bytecode = True

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def build_manifest(packet):
    entries = {}
    for r, dirs, files in os.walk(packet):
        dirs.sort()
        entries[os.path.normpath(os.path.relpath(r, packet))] = {"type": "dir"}
        for f in sorted(files):
            p = os.path.join(r, f)
            rel = os.path.normpath(os.path.relpath(p, packet))
            if rel == "MANIFEST.json":
                continue
            with open(p, "rb") as fh:
                b = fh.read()
            entries[rel] = {"type": "file", "bytes": len(b), "sha256": hashlib.sha256(b).hexdigest()}
    return {"version": 1, "entries": dict(sorted(entries.items()))}


def write_manifest(root):
    packet = os.path.join(root, "packet")
    with open(os.path.join(packet, "MANIFEST.json"), "w") as fh:
        json.dump(build_manifest(packet), fh, indent=1)
        fh.write("\n")
    return sha256_file(os.path.join(packet, "MANIFEST.json"))


def write_final(root, author_finalhash):
    with open(os.path.join(root, "packet/public/verdict.json"), "rb") as fh:
        verdict = json.loads(fh.read())["verdict"]
    final = {
        "version": 1,
        "candidate": "T106O133",
        "review": "contribution-r1",
        "status": "SEALED_CONTRIBUTION_REVIEW",
        "verdict": verdict,
        "conditional_on_correctness": True,
        "assigns": {"correctness_gate": False, "acceptance": False, "count": False},
        "pin": PIN,
        "provider": "Factory Droid",
        "model": "claude-opus-5-5",
        "author_final_sha256": author_finalhash.lower(),
        "manifest_sha256": sha256_file(os.path.join(root, "packet/MANIFEST.json")),
        "report_sha256": sha256_file(os.path.join(root, "REPORT.md")),
        "review_sha256": sha256_file(os.path.join(root, "packet/public/review.md")),
        "verdict_sha256": sha256_file(os.path.join(root, "packet/public/verdict.json")),
        "input_fingerprints_sha256": sha256_file(os.path.join(root, "packet/public/input-fingerprints.json")),
    }
    with open(os.path.join(root, "FINAL.json"), "w") as fh:
        json.dump(final, fh, indent=1)
        fh.write("\n")
    return sha256_file(os.path.join(root, "FINAL.json"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["manifest", "final"])
    ap.add_argument("--root", required=True)
    ap.add_argument("--author-finalhash")
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    if a.mode == "manifest":
        print("MANIFEST sha256", write_manifest(root))
    else:
        if not a.author_finalhash:
            raise SystemExit("--author-finalhash is required")
        print("FINAL sha256", write_final(root, a.author_finalhash))


if __name__ == "__main__":
    main()
