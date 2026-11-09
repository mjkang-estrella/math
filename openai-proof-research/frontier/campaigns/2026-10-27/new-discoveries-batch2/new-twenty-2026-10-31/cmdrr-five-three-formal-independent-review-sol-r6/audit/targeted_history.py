import json,pathlib,base64,hashlib
p=pathlib.Path.cwd()
for f in ["inputs/source/registry-and-pinned-inventory.json","inputs/author/audit/PROCESS-INVENTORY.json"]:
 print(f,(p/f).read_text())
for f,keys in [
("inputs/root/HISTORICAL-R3-INTEGRATION.json",["actual_state","source_only_baseline_order","root_status","root_disposition","historical_process_breach","prospective_repair_not_waiver","body_origin_limits","prior_limit"]),
("inputs/root/AUTHOR-R4-INTEGRATION.json",["retained_process_limits","prior_limits","historical_breach","root_status","root_scope","independent_review_required"]),
("inputs/root/INDEPENDENT-R5-INTEGRATION.json",["root_status","root_disposition","independent_review_required","retained_process_limits"])]:
 d=json.loads((p/f).read_text());print(f,json.dumps({k:d.get(k) for k in keys},ensure_ascii=False,indent=2))
for f in ["inputs/source/literal-provenance.json","inputs/source/original-twenty.jsonl"]:
 raw=(p/f).read_text();d=json.loads(raw) if f.endswith(".json") else [json.loads(l) for l in raw.splitlines()]
 target=[x for x in d if x.get("id",x.get("mathdb_id"))==326555]
 print("TARGET",f,json.dumps(target,ensure_ascii=False,indent=2))
print("registry prior",json.dumps({k:v for k,v in json.loads((p/"inputs/source/prior-reconciliation.json").read_text()).items() if k!="reads"},ensure_ascii=False))

