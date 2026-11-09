import json, hashlib, os
ROOT="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes"
LANE=ROOT+"/pi-mathdb-primary-first-breadth-r314"
CORPUS=ROOT+"/pi-mathdb-full-corpus-inventory-r301/corpus"
ids=json.load(open(ROOT+"/root-mathdb-inventory-intake-r311/next-breadth-ids.json"))
assert len(ids)==50, len(ids)
want=set(ids)
found={}
chunks={}
for fn in sorted(os.listdir(CORPUS)):
    if not fn.endswith(".jsonl"): continue
    p=os.path.join(CORPUS,fn)
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for line in f:
            h.update(line)
            if line.startswith(b'{'):
                try: rec=json.loads(line)
                except Exception: continue
                rid=rec.get("mathdb_id")
                if rid in want:
                    found.setdefault(rid,[]).append(fn)
    chunks[fn]=h.hexdigest()
missing=[i for i in ids if i not in found]
dupes={k:v for k,v in found.items() if len(v)>1}
out={"schema_version":1,"lane":"pi-mathdb-primary-first-breadth-r314",
 "reserved_ids":ids,
 "chunk_sha256":chunks,
 "id_to_chunk":{str(k):v for k,v in found.items()},
 "missing":missing,
 "duplicates":dupes}
json.dump(out,open(LANE+"/source-bindings.json","w"),indent=1)
print("missing:",missing)
print("dupes:",dupes)
print("n_found:",len(found))
