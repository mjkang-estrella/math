#!/usr/bin/env python3
"""Freeze the r332 frozen delivery BEFORE content review.

Enumerates ALL files under the r332 frozen tree (no exclusions, __pycache__
included), hashes each with sha256, records size, and cross-checks every
entry that appears in the root manifest.json (path, bytes, sha256).
Also records actual UTC now, and any extra/missing files relative to the
root manifest file list. Exits nonzero on any mismatch.
"""
import hashlib
import json
import os
import sys

LANES = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ROOT = os.path.join(LANES, "root-mathdb-breadth-intake-r332")
FROZEN = os.path.join(ROOT, "frozen")
OUT = os.path.join(LANES, "pi-cayley-avoidance-preliminary-review-r333", "work",
                   "frozen-delivery-manifest.json")


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    now = __import__("datetime").datetime.now(__import__("datetime").timezone.utc)
    actual = {}
    for dirpath, dirnames, filenames in os.walk(FROZEN):
        for name in sorted(filenames):
            p = os.path.join(dirpath, name)
            rel = os.path.relpath(p, FROZEN)
            st = os.stat(p)
            actual[rel] = {"bytes": st.st_size, "sha256": sha256_file(p)}

    with open(os.path.join(FROZEN, "manifest.json")) as f:
        manifest = json.load(f)

    claimed = {e["path"]: e for e in manifest["files"]}
    checked, mismatches, extras, missing = [], [], [], []
    documented_exclusions = set(manifest.get("excluded_by_exact_relative_name", []))
    excluded_but_hashed = {}
    for rel, got in sorted(actual.items()):
        if rel == "manifest.json":
            continue  # manifest itself not self-listed; cross-checked via claims below
        if rel in documented_exclusions and rel not in claimed:
            excluded_but_hashed[rel] = got
            continue
        if rel not in claimed:
            extras.append(rel)
            continue
        c = claimed[rel]
        ok = (c["bytes"] == got["bytes"] and c["sha256"] == got["sha256"])
        checked.append({"path": rel, "bytes": got["bytes"], "sha256": got["sha256"],
                        "matches_root_manifest": ok})
        if not ok:
            mismatches.append(rel)
    for rel in sorted(claimed):
        if rel not in actual:
            missing.append(rel)

    report = {
        "generated_at_utc": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "frozen_root": ROOT,
        "files_hashed": len(actual),
        "cross_checked_against_root_manifest": True,
        "checked": checked,
        "documented_exclusions_hashed": excluded_but_hashed,
        "extra_files_not_in_root_manifest": extras,
        "missing_files_from_root_manifest": missing,
        "mismatches": mismatches,
        "all_match": not mismatches and not missing and not extras,
    }
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as f:
        json.dump(report, f, indent=2, sort_keys=True)
    print(json.dumps({
        "files_hashed": len(actual),
        "mismatches": mismatches,
        "missing": missing,
        "extras": extras,
        "excluded_but_hashed": sorted(excluded_but_hashed),
        "all_match": report["all_match"],
    }, indent=2))
    sys.exit(0 if report["all_match"] else 1)


if __name__ == "__main__":
    main()
