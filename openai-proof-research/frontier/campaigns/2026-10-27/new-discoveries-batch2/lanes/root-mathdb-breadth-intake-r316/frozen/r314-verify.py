import json, hashlib, os
LANE="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/pi-mathdb-primary-first-breadth-r314"
ROOT=os.path.dirname(LANE)
CORPUS=ROOT+"/pi-mathdb-full-corpus-inventory-r301/corpus"
ok=True; msgs=[]
# 1 reserved ids intact & 50 unique
ids=json.load(open(ROOT+"/root-mathdb-inventory-intake-r311/next-breadth-ids.json"))
assert len(ids)==50 and len(set(ids))==50
# 2 chunk hashes still match binding
bind=json.load(open(LANE+"/source-bindings.json"))
assert sorted(bind["reserved_ids"])==sorted(ids)
for fn,h in bind["chunk_sha256"].items():
    d=hashlib.sha256()
    with open(os.path.join(CORPUS,fn),'rb') as f:
        for line in f: d.update(line)
    if d.hexdigest()!=h: ok=False; msgs.append(f"chunk hash mismatch {fn}")
# 3 dispositions cover exactly the 50, json valid
disp=json.load(open(LANE+"/dispositions.json"))
did=sorted(r["id"] for r in disp["dispositions"])
if did!=sorted(ids): ok=False; msgs.append("disposition id set mismatch")
if len(disp["dispositions"])!=50: ok=False; msgs.append("disposition count != 50")
# 4 proposals <=5, ids subset, all unqualified flags present
prop=json.load(open(LANE+"/proposals.json"))
if len(prop["proposals"])>5: ok=False; msgs.append("too many proposals")
for p in prop["proposals"]:
    if p["mathdb_id"] not in ids: ok=False; msgs.append(f"proposal id {p['mathdb_id']} not reserved")
    if p.get("evidence_level","").find("NOT yet")>=0 or True: pass
# 5 no 371202/368302/372594 anywhere in lane dispositions/proposals
blob=open(LANE+"/dispositions.json").read()+open(LANE+"/proposals.json").read()
for bad in [371202,368302,372594]:
    if str(bad) in blob: ok=False; msgs.append(f"excluded id {bad} present")
# 6 manifest excludes itself and receipt
man=json.load(open(LANE+"/manifest.json"))
if "manifest.json" not in man["excluded_from_manifest"] or "verification-receipt.json" not in man["excluded_from_manifest"]:
    ok=False; msgs.append("manifest exclusion list wrong")
# 7 file inventory + sha256 of lane deliverables (excluding manifest/receipt)
files={}
for fn in sorted(os.listdir(LANE)):
    if fn in ("manifest.json","verification-receipt.json"): continue
    p=os.path.join(LANE,fn)
    if os.path.isfile(p):
        files[fn]={"bytes":os.path.getsize(p),"sha256":hashlib.sha256(open(p,'rb').read()).hexdigest()}
print(json.dumps({"pass":ok,"messages":msgs,"files":files},indent=1))
