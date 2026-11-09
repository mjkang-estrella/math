import json
from pathlib import Path

R = Path(__file__).resolve().parent.parent
L = R.parent.parent / "lanes"
INTAKE = L / "root-mathdb-breadth-intake-r338"
INV = L / "pi-mathdb-full-corpus-inventory-r301"
EXCL = L / "root-mathdb-accepted-exclusions-r304"

ids = json.loads((INTAKE / "reserved-ids.json").read_text())["ids"]
want = set(ids)
assert len(want) == 50

found = {}
chunks = sorted((INV / "corpus").glob("mathdb-normalized-chunk-*.jsonl"))
for c in chunks:
    for line in c.read_text().splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        if r["mathdb_id"] in want:
            found[r["mathdb_id"]] = r

missing = want - set(found)
assert not missing, f"missing: {sorted(missing)}"

# mandatory scope dedup AFTER binding: prior coverage, accepted exclusions, historical dispositions
cov = json.loads((INTAKE / "coverage-delta.json").read_text())
acc = json.loads((EXCL / "accepted-exclusions.json").read_text())
hist = json.loads((EXCL / "historical-dispositions.json").read_text())

def idsets(x):
    if isinstance(x, dict):
        return set(map(str, x.keys()))
    out = set()
    for e in x:
        for k in ("mathdb_id", "id"):
            if k in e:
                out.add(str(e[k]))
    return out

acc_ids = idsets(acc) if not isinstance(acc, dict) else set(map(str, acc.keys()))
hist_ids = idsets(hist) if not isinstance(hist, dict) else set(map(str, hist.keys()))
res_ids = set(map(str, ids))
print("overlap with 283 prior coverage:", sorted(res_ids & set(map(str, cov.keys()))))
print("overlap with accepted-exclusions:", sorted(res_ids & acc_ids))
print("overlap with historical-dispositions:", sorted(res_ids & hist_ids))
if isinstance(acc, dict):
    for k in sorted(res_ids & acc_ids):
        print("  exclusion detail", k, json.dumps(acc[k])[:300])
if isinstance(hist, dict):
    for k in sorted(res_ids & hist_ids):
        print("  historical detail", k, json.dumps(hist[k])[:300])

with (R / "sources" / "reserved-records.jsonl").open("w") as f:
    for i in ids:
        f.write(json.dumps(found[i], sort_keys=True) + "\n")
print("extracted", len(found), "records")
for i in ids:
    r = found[i]
    print(i, "|", r["post_type"], "|", r["status"], "|", r.get("statement_completeness"), "| sol:", r.get("solution_count"), "|", r["title"][:80])
