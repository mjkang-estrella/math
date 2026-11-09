import json,hashlib,os
BASE="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2"
CORPUS=BASE+"/lanes/pi-mathdb-full-corpus-inventory-r301"
LANE=BASE+"/lanes/pi-mathdb-primary-qualified-breadth-r327"
def sha(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): h.update(b)
    return h.hexdigest()
m=json.load(open(LANE+"/frozen/r301-manifest.json"))
chunks=[f for f in m['files'] if 'corpus/' in f['path']]
assert len(chunks)==20, len(chunks)
# bind hashes BEFORE reading: verify each in place
verified=[]
for f in chunks:
    p=os.path.join(CORPUS,f['path'])
    s=sha(p)
    ok = s==f['sha256'] and os.path.getsize(p)==f['bytes']
    verified.append({"path":f['path'],"sha256":s,"bytes":os.path.getsize(p),"match":ok})
    assert ok, f['path']
json.dump(verified,open(LANE+"/work/corpus-verification.json","w"),indent=1)
reserved=set(json.load(open(LANE+"/frozen/reserved-ids.json")))
found={}
for f in chunks:
    p=os.path.join(CORPUS,f['path'])
    with open(p) as fh:
        for line in fh:
            try: rec=json.loads(line)
            except Exception: continue
            mid=rec.get('mathdb_id') or rec.get('id')
            if mid in reserved and mid not in found:
                found[mid]=rec
missing=reserved-set(found.keys())
extra=set(found.keys())-reserved
json.dump({"records":found,"missing":sorted(missing),"extra":sorted(extra),"chunks_verified":len(verified)},
          open(LANE+"/work/reserved-records.json","w"))
print("found",len(found),"missing",sorted(missing),"extra",sorted(extra))
