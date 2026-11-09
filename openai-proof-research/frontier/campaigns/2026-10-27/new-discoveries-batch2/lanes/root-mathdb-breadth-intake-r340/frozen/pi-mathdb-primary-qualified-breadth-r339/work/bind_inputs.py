import hashlib, json, sys, datetime
from pathlib import Path

R = Path(__file__).resolve().parent.parent          # lane root
B = R.parent.parent                                 # campaign root (new-discoveries-batch2)
L = B / "lanes"
INTAKE = L / "root-mathdb-breadth-intake-r338"
INV    = L / "pi-mathdb-full-corpus-inventory-r301"
EXCL   = L / "root-mathdb-accepted-exclusions-r304"

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

entries = []

def bind(original, manifest=None, rel=None):
    p = Path(original)
    h, s = sha(p), p.stat().st_size
    e = {"original": str(p), "ref": "in-place", "sha256": h, "size": s}
    if manifest is not None:
        mm = json.loads(Path(manifest).read_text())
        files = mm["files"] if isinstance(mm, dict) else mm
        exp = next(x for x in files if x["path"] == rel)
        assert exp["sha256"] == h, f"manifest mismatch: {rel}"
        if "bytes" in exp: assert exp["bytes"] == s, f"manifest size mismatch: {rel}"
        if "size" in exp: assert exp["size"] == s, f"manifest size mismatch: {rel}"
        e["manifest"] = {"path": str(Path(manifest)), "rel": rel}
    entries.append(e)
    return e

# r338 intake inputs (manifest already PASSed via intake verify.py)
for name in ["reserved-ids.json", "queue.json", "coverage-delta.json"]:
    bind(INTAKE / name, INTAKE / "manifest.json", name)

# corpus chunks 1..20 + inventory manifest, hashes compared BEFORE any content read
bind(INV / "manifest.json")
for i in range(1, 21):
    bind(INV / f"corpus/mathdb-normalized-chunk-{i:04d}.jsonl",
         INV / "manifest.json", f"corpus/mathdb-normalized-chunk-{i:04d}.jsonl")

# accepted exclusions (scope dedup, mandatory after binding)
for name in ["accepted-exclusions.json", "historical-dispositions.json"]:
    bind(EXCL / name, EXCL / "manifest.json", name)

out = {"bound_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
       "mode": "flat immutable in-place references (no corpus copies)",
       "bindings": entries}
(R / "bindings.json").write_text(json.dumps(out, indent=2) + "\n")
print(f"PASS bind {len(entries)} in-place references; corpus manifest cross-check OK (20 chunks); exclusions manifest cross-check OK")
