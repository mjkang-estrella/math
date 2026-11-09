#!/usr/bin/env python3
"""Independent final verifier for pi-mathdb-primary-qualified-breadth-r347.

Re-hashes every payload file listed in manifest.json against the ACTUAL bytes on disk
(not against build-time copies), checks the payload file set is exact and disjoint from
{manifest.json, verification-receipt.json}, re-checks reservation/coverage/exclusion
disjointness and the 50/0 disposition counts from the actual artifacts, and only then
writes verification-receipt.json with the ACTUAL UTC time of the check (never a build-time
placeholder). Exits NONZERO on any failure.

Run: OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B verify.py
"""
import json
import hashlib
import os
import sys
from datetime import datetime, timezone

LANE = os.path.dirname(os.path.abspath(__file__))
os.chdir(LANE)

EXCLUDED = {"manifest.json", "verification-receipt.json"}
failures = []


def fail(msg):
    failures.append(msg)


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# 1. manifest exists and is JSON with a files list
try:
    manifest = json.load(open("manifest.json"))
    entries = manifest["files"]
    if not isinstance(entries, list) or not entries:
        fail("manifest has no files list")
except Exception as e:
    fail(f"manifest unreadable: {e}")
    entries = []

# 2. exact payload set on disk vs manifest
declared = {e["path"] for e in entries}
actual = set()
for root, dirs, files in os.walk("."):
    dirs[:] = [d for d in dirs if d not in (".git", "__pycache__")]
    for fn in files:
        rel = os.path.relpath(os.path.join(root, fn), ".")
        if rel in EXCLUDED:
            continue
        actual.add(rel)

for p in sorted(declared - actual):
    fail(f"declared but missing: {p}")
for p in sorted(actual - declared):
    fail(f"on disk but not declared: {p}")

# 3. re-hash every declared payload from actual bytes
for e in entries:
    p = e["path"]
    if p not in actual:
        continue  # already failed above
    try:
        h = sha256_file(p)
        sz = os.path.getsize(p)
        if h != e["sha256"]:
            fail(f"hash mismatch: {p}")
        if sz != e["size"]:
            fail(f"size mismatch: {p}")
    except Exception as ex:
        fail(f"unreadable: {p}: {ex}")

# 4. semantic checks on the actual artifacts
try:
    reserved = json.load(open("frozen/root-mathdb-c5-intake-r346/reserved-ids.json"))["ids"]
    if len(reserved) != 50:
        fail(f"reserved ids != 50: {len(reserved)}")
    cov = set(json.load(open("frozen/root-mathdb-c5-intake-r346/coverage-delta.json")).keys())
    overlap_rc = {i for i in reserved if str(i) in cov}
    if overlap_rc:
        fail(f"reserved/coverage overlap: {sorted(overlap_rc)}")
    hd = json.load(open("frozen/root-mathdb-accepted-exclusions-r304/historical-dispositions.json"))

    def collect_ids(obj, acc):
        if isinstance(obj, int):
            acc.add(obj)
        elif isinstance(obj, dict):
            for k, v in obj.items():
                if k in ("mathdb_id", "id") and isinstance(v, int):
                    acc.add(v)
                else:
                    collect_ids(v, acc)
        elif isinstance(obj, list):
            for x in obj:
                collect_ids(x, acc)

    hist_ids = set()
    collect_ids(hd, hist_ids)
    overlap_h = {i for i in reserved if i in hist_ids}
    if overlap_h:
        fail(f"reserved/historical overlap: {sorted(overlap_h)}")
    ae = json.load(open("frozen/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json"))
    ae_ids = {int(k) for k in ae.get("mathdb_lookup", {}).keys()}
    overlap_a = {i for i in reserved if i in ae_ids}
    if overlap_a:
        fail(f"reserved/accepted-exclusions overlap: {sorted(overlap_a)}")

    disp = json.load(open("dispositions.json"))
    keys = set(disp["dispositions"].keys())
    if keys != {str(i) for i in reserved}:
        fail("dispositions keys != reserved ids")
    if disp["counts"]["total"] != 50:
        fail("dispositions total != 50")
    prop = json.load(open("proposals.json"))
    if len(prop["proposals"]) > 3:
        fail("more than 3 proposals")

    # frozen input hashes must still match the frozen bytes
    for line in open("frozen/input-hashes.txt"):
        line = line.strip()
        if not line:
            continue
        h, path = line.split("  ", 1)
        rel = os.path.relpath(os.path.join("frozen", path.lstrip("./")), ".")
        if rel == "frozen/input-hashes.txt":
            continue  # self-referential entry omitted by design
        if not os.path.exists(rel):
            fail(f"frozen input missing: {rel}")
        elif sha256_file(rel) != h:
            fail(f"frozen input hash drift: {rel}")
except Exception as ex:
    fail(f"semantic checks errored: {ex}")

# 5. verdict + receipt written ONLY after all checks
status = "PASS" if not failures else "FAIL"
receipt = {
    "at": datetime.now(timezone.utc).isoformat(),
    "lane": "pi-mathdb-primary-qualified-breadth-r347",
    "status": status,
    "payload_files": len(entries),
    "checks": {
        "manifest_rehash": "done against actual bytes on disk",
        "exact_payload_set": "declared == on-disk, excluding manifest.json/verification-receipt.json",
        "reserved_vs_coverage_disjoint": "checked",
        "reserved_vs_historical_and_accepted_disjoint": "checked",
        "dispositions_exact_50": "checked",
        "proposals_le_3": "checked",
        "frozen_input_hashes_rechecked": "checked",
    },
    "failures": failures,
}
print(json.dumps({"status": status, "failures": failures, "payload_files": len(entries)}, indent=1))
with open("verification-receipt.json", "w") as f:
    json.dump(receipt, f, indent=1)
sys.exit(0 if not failures else 1)
