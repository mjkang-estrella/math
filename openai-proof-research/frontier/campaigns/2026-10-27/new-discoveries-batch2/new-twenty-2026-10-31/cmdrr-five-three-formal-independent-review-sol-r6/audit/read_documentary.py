import json,pathlib
p=pathlib.Path.cwd()
for f in ["inputs/source/accepted55-routing.json","inputs/source/prior39-routing.json","inputs/source/registry-and-pinned-inventory.json","inputs/source/prior-reconciliation.json","inputs/author/audit/PROCESS-INVENTORY.json","inputs/root/HISTORICAL-R3-INTEGRATION.json","inputs/root/AUTHOR-R4-INTEGRATION.json","inputs/independent-review-r5/results/FRESH-REPLAY.json","inputs/independent-review-r5/SHA256-MANIFEST.json"]:
 d=json.loads((p/f).read_text())
 print(f, "TYPE",type(d).__name__)
 print(list(d)[:30] if isinstance(d,dict) else (len(d),d[:1]))
for f in ["inputs/source/accepted55-routing.json","inputs/source/prior39-routing.json"]:
 d=json.loads((p/f).read_text())
 print("SCOPES",f,json.dumps(d,ensure_ascii=False))
for f in ["inputs/root/HISTORICAL-R3-INTEGRATION.json","inputs/root/AUTHOR-R4-INTEGRATION.json","inputs/root/INDEPENDENT-R5-INTEGRATION.json"]:
 d=json.loads((p/f).read_text());print("ADJUDICATION",f,json.dumps({k:v for k,v in d.items() if k not in ["receipts","files"]},ensure_ascii=False))
print("PROCESS", (p/"inputs/author/audit/PROCESS-INVENTORY.json").read_text())

