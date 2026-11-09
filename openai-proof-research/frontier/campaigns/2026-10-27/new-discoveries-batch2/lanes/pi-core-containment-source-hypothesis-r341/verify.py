"""Independent integrity verifier for lane pi-core-containment-source-hypothesis-r341.
Integrity ONLY (hashes/sizes/payload set/provenance binding) — not math or novelty.

Usage: python3 verify.py build   -> writes manifest.json over all payloads
       python3 verify.py verify  -> rehashes upstream originals (flat references),
                                    retained sources vs sources/provenance.json,
                                    and the exact payload set vs manifest.json;
                                    writes verification-receipt.json; NONZERO exit on failure.
Excluded from the payload set, by exact relative path: manifest.json, verification-receipt.json.
"""
import hashlib, json, sys
from pathlib import Path

R = Path(__file__).resolve().parent
EXCLUDE = {"manifest.json", "verification-receipt.json"}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def payload():
    return {str(p.relative_to(R)) for p in R.rglob("*") if p.is_file()} - EXCLUDE

def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)

bindings = json.loads((R / "bindings.json").read_text())

# 1. Upstream originals (flat references): rehash in place.
for e in bindings["bindings"]:
    p = Path(e["original"])
    if not p.is_file():
        fail(f"upstream original missing: {p}")
    if "sha256" in e and (sha(p) != e["sha256"] or p.stat().st_size != e["size"]):
        fail(f"upstream original hash/size mismatch: {p}")

# 2. Dedup result must record zero overlap for 393907.
if bindings.get("dedup_result", {}).get("mathdb_393907_overlap") is not False:
    fail("dedup_result missing or overlap not False")

prov = json.loads((R / "sources" / "provenance.json").read_text())
retained = {}
for s in prov["retained_sources"]:
    p = R / s["file"]
    if not p.is_file():
        fail(f"retained source missing: {s['file']}")
    if sha(p) != s["sha256"] or p.stat().st_size != s["size"]:
        fail(f"retained source hash/size mismatch vs provenance: {s['file']}")
    retained[s["file"]] = (s["sha256"], s["size"])

if sys.argv[1] == "build":
    files = [{"path": s, "sha256": sha(R / s), "size": (R / s).stat().st_size}
             for s in sorted(payload())]
    (R / "manifest.json").write_text(json.dumps({"files": files}, indent=1) + "\n")
    print("BUILD PASS:", len(files), "payloads;", len(bindings["bindings"]), "upstream refs;",
          len(retained), "retained sources")
    sys.exit(0)

if sys.argv[1] != "verify":
    fail("usage: build | verify")

# 3. Exact payload set vs manifest.
own = json.loads((R / "manifest.json").read_text())["files"]
if payload() != {e["path"] for e in own}:
    fail("payload set differs from manifest.json")
for e in own:
    p = R / e["path"]
    if sha(p) != e["sha256"] or p.stat().st_size != e["size"]:
        fail(f"payload hash/size mismatch: {e['path']}")

# 4. Verifier itself must be inside the manifest (it is a payload).
if "verify.py" not in {e["path"] for e in own}:
    fail("verify.py not covered by manifest")

# 5. Cross-check artifact must exist inside payloads with zero anomalies.
xc = R / "sources" / "crosscheck-maximal-beta-set.json"
if not xc.is_file():
    fail("crosscheck artifact missing")
data = json.loads(xc.read_text())
if data.get("anomalies") != [] or data.get("pairs_checked") != 15:
    fail("crosscheck artifact unexpected content")

# 6. Disposition must pin gate levels.
d = json.loads((R / "disposition.json").read_text())
if d.get("disposition") != "retired_public_resolution" or d.get("credit") != 0 \
   or d.get("source_record", {}).get("source_gate_level") != "PRIMARY_BODY_RETAINED" \
   or d.get("hypothesis_gate_level") != "PUBLICLY_RESOLVED_BODY_CONFIRMED":
    fail("disposition gate fields unexpected")

import datetime
(R / "verification-receipt.json").write_text(json.dumps({
    "status": "PASS",
    "at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "scope": "hash/size/payload-set integrity and provenance binding only; not math or novelty validation",
    "upstream_originals_rehashed": len(bindings["bindings"]),
    "retained_sources_rehashed": len(retained),
    "payloads": len(own),
    "crosscheck_pairs": 15,
    "counts_changed": False,
}, indent=1) + "\n")
print("VERIFY PASS:", len(own), "payloads,", len(bindings["bindings"]),
      "upstream originals,", len(retained), "retained sources")
