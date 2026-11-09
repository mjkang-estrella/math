import json,pathlib,base64,hashlib
p=pathlib.Path.cwd()
for f,keys in [
("inputs/author/audit/PROCESS-INVENTORY.json",["telemetry","other_deviations","historical_r3"]),
("inputs/root/HISTORICAL-R3-INTEGRATION.json",["root_status","root_disposition","historical_process_breach","prospective_repair_not_waiver","body_origin_limits","prior_limit"]),
("inputs/root/AUTHOR-R4-INTEGRATION.json",["retained_process_limits","prior_limits","historical_breach","root_status","root_scope","independent_review_required"])]:
 d=json.loads((p/f).read_text());print(f,json.dumps({k:d.get(k) for k in keys},ensure_ascii=False,indent=2))
d=json.loads((p/"inputs/source/literal-provenance.json").read_text())
target=next(x for x in d if x.get("id")==326555)
print("TARGET PROVENANCE",json.dumps(target,ensure_ascii=False))
orig=[json.loads(l) for l in (p/"inputs/source/original-twenty.jsonl").read_text().splitlines()]
print("ORIGINAL20 TARGET",json.dumps([x for x in orig if x.get("mathdb_id",x.get("id"))==326555],ensure_ascii=False))
print("MATCHES",json.dumps(json.loads((p/"inputs/source/prior-reconciliation.json").read_text())["matches"]))
print("OWN R5 manifest schema",str(json.loads((p/"inputs/independent-review-r5/SHA256-MANIFEST.json").read_text())["files"])[:1000])
print("R5 fresh shape",str(json.loads((p/"inputs/independent-review-r5/results/FRESH-REPLAY.json").read_text()))[:2000])

