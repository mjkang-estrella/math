#!/usr/bin/env python3
"""Post-write verification for lane pi-cayley-avoidance-preliminary-review-r333.

Checks, in order:
  1. Re-hash EVERY file under this lane (os.walk, __pycache__ and hidden
     files included) and compare path/bytes/sha256 against
     review-manifest.json. Exact-relative-path exclusions:
     {verify.py, verification-receipt.json, review-manifest.json}.
     Any extra file not in the manifest, any missing file, and any hash or
     size mismatch is a FAILURE.
  2. Re-hash the three primary source ORIGINALS in
     root-mathdb-breadth-intake-r332/frozen/sources/ against BOTH the root
     manifest entries and this lane's work/frozen-delivery-manifest.json
     entries (originals and the recorded delivery must agree).
  3. On success: write verification-receipt.json (real UTC clock) and exit 0.
     On any failure: write verification-receipt-failed.json, print the
     failure list, and EXIT NONZERO.

This verifier never trusts recorded booleans; it rehashes bytes itself.
"""
import hashlib
import json
import os
import sys
from datetime import datetime, timezone

LANE = os.path.dirname(os.path.abspath(__file__))
LANES = os.path.dirname(LANE)
R332_FROZEN = os.path.join(LANES, "root-mathdb-breadth-intake-r332", "frozen")
PRIMARY = ["sources/2407.19583v1.html", "sources/2407.19583-abs.html",
           "sources/ajc_v94_p267.pdf"]
SELF_EXCLUDED = {"verify.py", "verification-receipt.json", "review-manifest.json"}


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def now():
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def main():
    failures = []

    # ---- 1. lane files vs manifest
    with open(os.path.join(LANE, "review-manifest.json")) as f:
        manifest = json.load(f)
    claimed = {e["path"]: e for e in manifest["files"]}
    actual = {}
    for dirpath, dirnames, filenames in os.walk(LANE):
        for name in filenames:
            p = os.path.join(dirpath, name)
            rel = os.path.relpath(p, LANE)
            if rel in SELF_EXCLUDED:
                continue
            actual[rel] = {"bytes": os.path.getsize(p), "sha256": sha256_file(p)}
    for rel in sorted(actual):
        if rel not in claimed:
            failures.append({"check": "lane_files", "file": rel,
                             "error": "present but not in manifest"})
    for rel in sorted(claimed):
        if rel not in actual:
            failures.append({"check": "lane_files", "file": rel,
                             "error": "in manifest but missing on disk"})
    for rel, got in sorted(actual.items()):
        c = claimed.get(rel)
        if c and (c["sha256"] != got["sha256"] or c["bytes"] != got["bytes"]):
            failures.append({"check": "lane_files", "file": rel,
                             "error": "hash/size mismatch",
                             "expected": [c["bytes"], c["sha256"]],
                             "actual": [got["bytes"], got["sha256"]]})

    # ---- 2. primary originals: root manifest vs frozen-delivery-manifest
    with open(os.path.join(R332_FROZEN, "manifest.json")) as f:
        root_manifest = json.load(f)
    root_claims = {e["path"]: e for e in root_manifest["files"]}
    with open(os.path.join(LANE, "work", "frozen-delivery-manifest.json")) as f:
        fdm = json.load(f)
    fdm_claims = {e["path"]: e for e in fdm["checked"]}
    for rel in PRIMARY:
        p = os.path.join(R332_FROZEN, rel)
        if not os.path.exists(p):
            failures.append({"check": "primary_originals", "file": rel,
                             "error": "original missing"})
            continue
        got = {"bytes": os.path.getsize(p), "sha256": sha256_file(p)}
        rc = root_claims.get(rel)
        fc = fdm_claims.get(rel)
        if not rc or rc["sha256"] != got["sha256"] or rc["bytes"] != got["bytes"]:
            failures.append({"check": "primary_originals_vs_root_manifest",
                             "file": rel, "actual": got})
        if not fc or fc["sha256"] != got["sha256"] or fc["bytes"] != got["bytes"]:
            failures.append({"check": "primary_originals_vs_frozen_delivery_manifest",
                             "file": rel, "actual": got})

    # ---- 3. receipt
    receipt = {
        "lane": "pi-cayley-avoidance-preliminary-review-r333",
        "verified_at_utc": now(),
        "manifest": "review-manifest.json",
        "manifest_sha256": sha256_file(os.path.join(LANE, "review-manifest.json")),
        "lane_files_checked": len(actual),
        "primary_originals_rehashed": PRIMARY,
        "failures": failures,
        "result": "PASS" if not failures else "FAIL",
    }
    if failures:
        with open(os.path.join(LANE, "verification-receipt-failed.json"), "w") as f:
            json.dump(receipt, f, indent=2)
        print(json.dumps(receipt, indent=2), file=sys.stderr)
        print("VERIFICATION FAILED: %d failures" % len(failures), file=sys.stderr)
        sys.exit(1)
    with open(os.path.join(LANE, "verification-receipt.json"), "w") as f:
        json.dump(receipt, f, indent=2)
    print(json.dumps(receipt, indent=1))
    print("VERIFICATION PASSED", file=sys.stderr)


if __name__ == "__main__":
    main()
