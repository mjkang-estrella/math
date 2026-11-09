from pathlib import Path
import json, hashlib, re, collections
p=Path(__file__).resolve().parent.parent
def sha(q): return hashlib.sha256(q.read_bytes()).hexdigest()
logs={q.name:q for q in (p/"inputs/author-logs").rglob("*.log")}
records=[]
for d in ["inputs/author-receipt","inputs/author-cleanroom-receipt"]:
 for q in sorted((p/d).glob("*.json")):
  r=json.loads(q.read_text()); leaf=Path(r["log"]).name; log=logs.get(leaf)
  records.append({"file":str(q.relative_to(p)),"label":r["label"],"stamp":r["stamp"],"end_ns":r["stamp"]+r["wall_ms"]*1000000,"exit":r["exit"],"log_found":log is not None,"log_hash_matches":sha(log)==r["log_sha256"] if log else None,"groups_empty":r["group_members_left"]==[]})
pairs=[]
for i,a in enumerate(records):
 for b in records[i+1:]:
  if max(a["stamp"],b["stamp"])<min(a["end_ns"],b["end_ns"]):
   pairs.append([a["file"],b["file"]])
inv=json.loads((p/"audit/independent-inventory.json").read_text())
local=[r for r in inv["declarations"] if r["local"]]
# Human-scale classification of EVERY local declaration; full types and bodies remain in inventory.
summary=[]
source_defs={}
for q in (p/"src").glob("*.lean"):
 for i,line in enumerate(q.read_text().splitlines(),1):
  m=re.search(r"\b(?:def|abbrev|theorem)\s+(\w+)",line)
  if m: source_defs[m[1]]=(str(q.relative_to(p)),i)
for r in local:
 short=r["name"].removeprefix("UnitCoset.")
 owners=[n for n in source_defs if short==n or short.startswith(n+".")]
 owner=max(owners,key=len) if owners else None
 assert owner is not None,r["name"]
 summary.append({"name":r["name"],"origin":r["origin"],"source_owner":owner,"source_anchor":source_defs[owner],"generated":short!=owner,"type_bytes":len(r["type"]),"body_bytes":len(r["body"]),"body_present":not r["body"].startswith("no value"),"local_dependencies":sorted(set(d for d in r["dependencies"] if d.startswith("UnitCoset."))),"unsafe":r["unsafe"],"axiom":r["axiom"]})
assert all(x["body_present"] and not x["unsafe"] and not x["axiom"] for x in summary)
out={"author_receipts":records,"overlap_intervals_sampled_from_stamp_wall":pairs,"author_unique_count":len(records),"author_exit_counts":dict(collections.Counter(str(x["exit"]) for x in records)),"declarations":summary,"typed_body_note":"Full Expr representations are saved and structurally traversed, not claimed manually read byte by byte. Every constant dependency from both type and body audited."}
(p/"results/process-and-declarations.json").write_text(json.dumps(out,indent=2))
print("AUTHOR",len(records),out["author_exit_counts"],"missing_logs",sum(not r["log_found"] for r in records),"bad_hash",sum(r["log_hash_matches"] is False for r in records))
print("OVERLAPS",pairs)
for r in summary: print(r["name"],"origin",r["origin"],"source",r["source_anchor"],"generated",r["generated"],"localdeps",r["local_dependencies"])
