import hashlib, json, sys, datetime, traceback
from pathlib import Path

R = Path(__file__).resolve().parent
EXCLUDE = {"manifest.json", "verification-receipt.json"}

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def fail(msg):
    print("VERIFY FAIL:", msg)
    sys.exit(1)

try:
    # 1. rehash actual original input references (in-place) against bindings.json
    bindings = json.loads((R / "bindings.json").read_text())
    n_ref = 0
    for e in bindings["bindings"]:
        p = Path(e["original"])
        if not p.exists() or sha(p) != e["sha256"] or p.stat().st_size != e["size"]:
            fail(f"input reference changed or missing: {e['original']}")
        n_ref += 1

    # 2. rehash retained source artifacts against their fetch-time hashes
    prov = json.loads((R / "sources/fetch-provenance.json").read_text())
    n_src = 0
    for item in prov["items"]:
        if "error" in item:
            continue
        p = R / item["path"]
        if not p.exists() or sha(p) != item["sha256"] or p.stat().st_size != item["bytes"]:
            fail(f"retained source changed or missing: {item['path']}")
        n_src += 1

    # 3. exact payload set and manifest rehash (includes verify.py itself)
    payload = {str(p.relative_to(R)) for p in R.rglob("*") if p.is_file() and str(p.relative_to(R)) not in EXCLUDE}
    manifest = json.loads((R / "manifest.json").read_text())
    listed = {e["path"] for e in manifest["files"]}
    if payload != listed:
        fail(f"file set mismatch: in_manifest_not_on_disk={sorted(listed - payload)} on_disk_not_in_manifest={sorted(payload - listed)}")
    for e in manifest["files"]:
        p = R / e["path"]
        if sha(p) != e["sha256"] or p.stat().st_size != e["size"]:
            fail(f"payload hash/size mismatch: {e['path']}")

    # 4. invariant re-checks: 50 exact reserved IDs, dedup, dispositions
    intake = R.parent / "root-mathdb-breadth-intake-r338"
    reserved = json.loads((intake / "reserved-ids.json").read_text())["ids"]
    cov = json.loads((intake / "coverage-delta.json").read_text())
    excl = R.parent / "root-mathdb-accepted-exclusions-r304"
    acc = json.loads((excl / "accepted-exclusions.json").read_text())
    hist = json.loads((excl / "historical-dispositions.json").read_text())
    disp = json.loads((R / "dispositions.json").read_text())
    dids = [d["mathdb_id"] for d in disp["dispositions"]]
    res = set(map(str, reserved))
    def keyset(x):
        return set(map(str, x.keys())) if isinstance(x, dict) else {str(e.get("mathdb_id", e.get("id"))) for e in x}
    if len(dids) != 50 or len(set(dids)) != 50 or set(map(str, dids)) != res:
        fail("dispositions do not cover exactly the 50 reserved IDs")
    if res & set(map(str, cov.keys())):
        fail("overlap with prior 283 coverage")
    if res & keyset(acc) or res & keyset(hist):
        fail("overlap with exclusion registries")
    recs = {json.loads(s)["mathdb_id"]: json.loads(s) for s in (R / "sources/reserved-records.jsonl").read_text().splitlines()}
    if {str(k) for k in recs} != res:
        fail("reserved-records.jsonl does not match reserved IDs")
    props = json.loads((R / "proposals.json").read_text())
    pb = [b["mathdb_id"] for b in props["briefs"]]
    if len(pb) > 3 or not {str(x) for x in pb} <= res:
        fail("proposals violate brief constraints")

    # 5. receipt
    (R / "verification-receipt.json").write_text(json.dumps({
        "status": "PASS",
        "at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "input_references_rehashed": n_ref,
        "retained_sources_rehashed": n_src,
        "payloads_rehashed": len(manifest["files"]),
        "dispositioned_ids": len(dids),
        "briefs": len(pb),
        "math_replay": False
    }, indent=1) + "\n")
    print(f"PASS verify: {n_ref} input references, {n_src} retained sources, {len(manifest['files'])} payloads, {len(dids)} dispositions, {len(pb)} briefs")
except SystemExit:
    raise
except Exception as e:
    traceback.print_exc()
    print("VERIFY FAIL: unexpected error:", repr(e))
    sys.exit(1)
