#!/usr/bin/env python3
"""verify.py — independent post-write comparison for r320.

Recomputes SHA-256 of every payload recorded in manifest.json and compares against
the recorded hashes. Exits NONZERO on any mismatch, missing file, or missing
manifest. Also checks the disjointness claim of the 50 reserved IDs against the
frozen r316 coverage overlay. No 'or True' readiness check: every failure path
exits 1.
"""
import hashlib, json, os, sys

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()

def main():
    errors = []
    mp = os.path.join(LANE, "manifest.json")
    if not os.path.isfile(mp):
        print("FAIL: manifest.json missing"); sys.exit(1)
    manifest = json.load(open(mp))
    if manifest.get("lane") != "pi-mathdb-primary-qualified-breadth-r320":
        errors.append("manifest lane mismatch")
    if not manifest.get("payloads"):
        errors.append("manifest has no payloads")
    seen = set()
    for entry in manifest["payloads"]:
        rel = entry["path"]
        if rel in seen:
            errors.append(f"duplicate manifest path {rel}")
        seen.add(rel)
        p = os.path.join(LANE, rel)
        if not os.path.isfile(p):
            errors.append(f"missing payload {rel}"); continue
        actual = sha256(p)
        if actual != entry["sha256"]:
            errors.append(f"hash mismatch {rel}: recorded {entry['sha256']} actual {actual}")
        if os.path.getsize(p) != entry["bytes"]:
            errors.append(f"size mismatch {rel}")
        if rel in ("manifest.json", "verification-receipt.json"):
            errors.append(f"excluded name present in manifest: {rel}")

    # structural checks
    for req in ["dispositions.json", "proposals.json", "SUMMARY.md", "bindings.json", "RUN"]:
        if not os.path.isfile(os.path.join(LANE, req)):
            errors.append(f"required deliverable missing: {req}")
    disp = json.load(open(os.path.join(LANE, "dispositions.json")))
    reserved = json.load(open(os.path.join(LANE, "frozen", "r318-reserved-ids.json")))
    dkeys = {int(k) for k in disp["dispositions"]}
    if dkeys != set(reserved):
        errors.append(f"dispositions coverage mismatch: missing {sorted(set(reserved)-dkeys)} extra {sorted(dkeys-set(reserved))}")
    delta = json.load(open(os.path.join(LANE, "frozen", "r316-coverage-delta.json")))
    overlap = sorted(set(reserved) & {int(k) for k in delta})
    if overlap:
        errors.append(f"reserved IDs overlap r316 coverage overlay: {overlap}")
    props = json.load(open(os.path.join(LANE, "proposals.json")))
    if len(props["proposals"]) > 3:
        errors.append("more than three proposals")
    for pr in props["proposals"]:
        if int(pr["mathdb_id"]) not in dkeys:
            errors.append(f"proposal id {pr['mathdb_id']} not in dispositions")

    if errors:
        print("VERIFY FAILED:")
        for e in errors: print(" -", e)
        sys.exit(1)
    print(f"VERIFY OK: {len(manifest['payloads'])} payloads match recorded SHA-256; "
          f"50/50 dispositions present; reserved set disjoint from r316 overlay; "
          f"{len(props['proposals'])} proposals (max 3).")
    sys.exit(0)

if __name__ == "__main__":
    main()
