#!/usr/bin/env python3
"""Post-write verifier for lane pi-wronskian-hermite-source-hypothesis-r323.

Run separately AFTER manifest.json is written:
    python3 -B verify.py
Exits 0 iff every listed payload's SHA256 and byte count matches, and no unlisted
payload files exist (manifest.json and verification-receipt.json excluded by exact name).
"""
import hashlib, json, os, sys

LANE = os.path.dirname(os.path.abspath(__file__))
EXCLUDED = {"manifest.json", "verification-receipt.json"}

def main():
    mf = os.path.join(LANE, "manifest.json")
    if not os.path.isfile(mf):
        print("FAIL: manifest.json missing"); return 2
    man = json.load(open(mf))
    listed = {p["path"]: p for p in man.get("payloads", [])}
    if not listed:
        print("FAIL: manifest lists no payloads"); return 2
    errors = []
    seen = set()
    for root, dirs, files in os.walk(LANE):
        for name in files:
            rel = os.path.relpath(os.path.join(root, name), LANE)
            if rel in EXCLUDED:
                continue
            if rel not in listed:
                errors.append(f"UNLISTED PAYLOAD: {rel}")
                continue
            seen.add(rel)
            b = open(os.path.join(root, name), "rb").read()
            h = hashlib.sha256(b).hexdigest()
            if h != listed[rel]["sha256"]:
                errors.append(f"HASH MISMATCH: {rel} expected {listed[rel]['sha256']} got {h}")
            if len(b) != listed[rel]["bytes"]:
                errors.append(f"SIZE MISMATCH: {rel} expected {listed[rel]['bytes']} got {len(b)}")
    for rel in listed:
        if rel not in seen:
            errors.append(f"MISSING FILE: {rel}")
    if errors:
        for e in errors:
            print("FAIL:", e)
        return 1
    print(f"VERIFY PASS: {len(listed)} payloads match SHA256+bytes; no unlisted payloads; manifest and receipt excluded by exact name.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
