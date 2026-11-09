#!/usr/bin/env python3
"""Final verifier for lane pi-c5-semisaturation-source-hypothesis-r345.

Usage:  python3 verify.py build   -> writes manifest.json (+verification-receipt.json)
        python3 verify.py verify  -> rehashes ALL original/ref/copy actual bytes and the
                                     exact payload set; exits NONZERO on any failure.

Checks, in order:
  1. every bindings.json reference: original AND copy exist, sizes and sha256 match;
  2. the payload set (all files under the lane except manifest.json and
     verification-receipt.json) equals exactly the manifest.json file list;
  3. every manifest entry's sha256+size matches the actual bytes on disk;
  4. the network-retained sources carry their recorded provenance hashes;
  5. verification-receipt.json agrees with the manifest state.
No existence-only inputs are accepted: every hashed path must have real bytes.
"""
import hashlib, json, os, sys

R = os.path.dirname(os.path.abspath(__file__))
EXCLUDE = {"manifest.json", "verification-receipt.json"}
EXPECTED_SOURCES = {
    "sources/owr-2011-01-combinatorics.pdf":
        "669acffc78ac85b9960af120c763b97d8dd5cda176c1416322d238592884dd2b",
    "frozen/root-mathdb-breadth-intake-r344/sources/furedi-kim-1103.0067v1-cycle-saturated.pdf":
        "1f049570ebbe0fbc760c0b6eb964044869bf74184ede791c91f8db78482df4ea",
    "extraction/es1_2.png":
        "2b2047756a947afe3de4bafd19376bc999f542b6f383c5a9c746ad8d7ae225d3",
}

def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()

def fail(msg):
    print("VERIFY-FAIL:", msg)
    sys.exit(1)

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "verify"

    bindings = json.load(open(os.path.join(R, "bindings.json")))
    for e in bindings["references"]:
        for p in (e["original"], e["copy"]):
            fp = os.path.join(R, p) if not os.path.isabs(p) else p
            if not os.path.isfile(fp):
                fail(f"missing binding file {p}")
            if os.path.getsize(fp) != e["size"] or sha(fp) != e["sha256"]:
                fail(f"binding hash/size mismatch {p}")

    def payload():
        out = set()
        for root, _, files in os.walk(R):
            for f in files:
                rel = os.path.relpath(os.path.join(root, f), R)
                if rel not in EXCLUDE:
                    out.add(rel.replace(os.sep, "/"))
        return out

    if mode == "build":
        entries = [{"path": p, "sha256": sha(os.path.join(R, p)),
                    "size": os.path.getsize(os.path.join(R, p))}
                   for p in sorted(payload())]
        json.dump({"files": entries}, open(os.path.join(R, "manifest.json"), "w"),
                  indent=2, sort_keys=True)
        json.dump({"verified_utc": "2026-10-31",
                   "note": "built by verify.py build; re-run 'verify' for the final check",
                   "payload_count": len(entries)},
                  open(os.path.join(R, "verification-receipt.json"), "w"), indent=2)
        print(f"BUILD OK: {len(entries)} payload entries")
        return

    manifest = json.load(open(os.path.join(R, "manifest.json")))
    entries = {e["path"]: e for e in manifest["files"]}
    actual = payload()
    if actual != set(entries):
        missing = actual - set(entries); extra = set(entries) - actual
        fail(f"payload set mismatch; missing-from-manifest={sorted(missing)} extra={sorted(extra)}")
    for p, e in entries.items():
        fp = os.path.join(R, p)
        if not os.path.isfile(fp):
            fail(f"manifest file missing on disk {p}")
        if os.path.getsize(fp) != e["size"] or sha(fp) != e["sha256"]:
            fail(f"hash/size mismatch {p}")

    for p, want in EXPECTED_SOURCES.items():
        if p not in entries:
            fail(f"expected retained source absent from manifest {p}")
        if entries[p]["sha256"] != want:
            fail(f"retained source hash drift {p}")

    receipt = json.load(open(os.path.join(R, "verification-receipt.json")))
    if receipt.get("payload_count") != len(entries):
        fail("verification-receipt payload_count disagrees with manifest")

    print(f"VERIFY OK: {len(entries)} payloads, {len(bindings['references'])} binding pairs, "
          f"{len(EXPECTED_SOURCES)} retained network sources — all bytes rehashed")

if __name__ == "__main__":
    main()
