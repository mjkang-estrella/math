#!/usr/bin/env python3
"""r320 freeze step: hash-verify and copy all admin/bound inputs BEFORE any
substantive read. Immutable sources only; no MathDB network access."""
import hashlib, json, os, shutil, sys, datetime

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LANES = os.path.dirname(LANE)  # lanes/
BASE = os.path.dirname(LANES)  # campaign root
R301 = os.path.join(LANES, "pi-mathdb-full-corpus-inventory-r301")
FROZEN = os.path.join(LANE, "frozen")
os.makedirs(FROZEN, exist_ok=True)

def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()

bindings = []

def freeze(src, copy_name):
    s, c = sha256(src), os.path.join(FROZEN, copy_name)
    shutil.copyfile(src, c)
    assert sha256(c) == s, f"copy mismatch {src}"
    bindings.append({"source": src, "copy": f"frozen/{copy_name}", "sha256": s,
                     "bytes": os.path.getsize(src)})

# Admin inputs (r318 reservation, r316 coverage delta, r304 exclusions)
for src, name in [
    (os.path.join(LANES, "root-mathdb-next-breadth-r318", "reserved-ids.json"), "r318-reserved-ids.json"),
    (os.path.join(LANES, "root-mathdb-next-breadth-r318", "queue.json"), "r318-queue.json"),
    (os.path.join(LANES, "root-mathdb-next-breadth-r318", "BRIEF.md"), "r318-BRIEF.md"),
    (os.path.join(LANES, "root-mathdb-breadth-intake-r316", "coverage-delta.json"), "r316-coverage-delta.json"),
    (os.path.join(LANES, "root-mathdb-accepted-exclusions-r304", "accepted-exclusions.json"), "r304-accepted-exclusions.json"),
    (os.path.join(LANES, "root-mathdb-accepted-exclusions-r304", "historical-dispositions.json"), "r304-historical-dispositions.json"),
    (os.path.join(LANES, "root-mathdb-accepted-exclusions-r304", "README.md"), "r304-README.md"),
    (os.path.join(LANES, "root-mathdb-fibonacci-intake-r319", "intake.json"), "r319-fibonacci-intake.json"),
]:
    freeze(src, name)

# Bind every corpus chunk (hash + copy) BEFORE reading any statement; verify
# against r301's recorded manifest hashes.
manifest = json.load(open(os.path.join(R301, "manifest.json")))
recorded = {f["path"]: f["sha256"] for f in manifest["files"]}
corpus_dir = os.path.join(R301, "corpus")
chunks = sorted(f for f in os.listdir(corpus_dir) if f.startswith("mathdb-normalized-chunk-"))
assert len(chunks) == 20, chunks
for fn in chunks:
    rel = f"corpus/{fn}"
    src = os.path.join(corpus_dir, fn)
    s = sha256(src)
    assert s == recorded[rel], f"chunk hash drift vs r301 manifest: {rel}"
    shutil.copyfile(src, os.path.join(FROZEN, fn))
    assert sha256(os.path.join(FROZEN, fn)) == s
    bindings.append({"source": src, "copy": f"frozen/{fn}", "sha256": s,
                     "bytes": os.path.getsize(src), "r301_manifest_match": True})

out = {"lane": "pi-mathdb-primary-qualified-breadth-r320",
       "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
       "bindings": bindings}
with open(os.path.join(LANE, "bindings.json"), "w") as f:
    json.dump(out, f, indent=2)
print(f"froze {len(bindings)} bindings OK")
