import json,hashlib,os
LANE="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/pi-mathdb-primary-qualified-breadth-r327"
EXCLUDE={"manifest.json","verification-receipt.json"}
def sha(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): h.update(b)
    return h.hexdigest()
files=[]
for root,dirs,fs in os.walk(LANE):
    dirs[:]=[d for d in dirs if d not in ("__pycache__",)]
    for f in sorted(fs):
        p=os.path.join(root,f)
        rel=os.path.relpath(p,LANE)
        if rel in EXCLUDE or "__pycache__" in rel: continue
        files.append({"path":rel,"bytes":os.path.getsize(p),"sha256":sha(p)})
files.sort(key=lambda x:x["path"])
json.dump({"lane":"pi-mathdb-primary-qualified-breadth-r327",
 "generated_at_utc":"2026-10-30T18:45:00Z",
 "excluded_by_exact_relative_name":["manifest.json","verification-receipt.json"],
 "files":files},open(os.path.join(LANE,"manifest.json"),"w"),indent=1)
print(len(files),"payloads")
