#!/usr/bin/env python3
"""Extract the 50 reserved full cached statements from frozen corpus chunks,
plus their r318 queue metadata rows, into work/ for review. Frozen bytes only."""
import json, os

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FROZEN = os.path.join(LANE, "frozen")
WORK = os.path.join(LANE, "work")
os.makedirs(WORK, exist_ok=True)

reserved = json.load(open(os.path.join(FROZEN, "r318-reserved-ids.json")))
assert len(reserved) == 50 and len(set(reserved)) == 50
want = set(reserved)
found = {}
chunks = sorted(f for f in os.listdir(FROZEN) if f.startswith("mathdb-normalized-chunk-"))
for fn in chunks:
    with open(os.path.join(FROZEN, fn), encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            rid = rec.get("id") or rec.get("mathdb_id")
            if rid in want:
                found.setdefault(rid, []).append({"chunk": fn, "record": rec})

missing = want - set(found)
dupes = {k: len(v) for k, v in found.items() if len(v) > 1}
print(f"found={len(found)} missing={sorted(missing)} dupes={dupes}")

with open(os.path.join(WORK, "reserved-records.json"), "w") as f:
    json.dump({"reserved_ids": sorted(want), "records": found}, f, indent=1, ensure_ascii=False)

# queue metadata
q = json.load(open(os.path.join(FROZEN, "r318-queue.json")))
rows = {r["mathdb_id"]: r for r in q.get("rows", [])}
with open(os.path.join(WORK, "reserved-queue-rows.json"), "w") as f:
    json.dump([rows[i] for i in sorted(want) if i in rows], f, indent=1, ensure_ascii=False)
print("queue rows matched:", sum(1 for i in want if i in rows), "/", 50)
