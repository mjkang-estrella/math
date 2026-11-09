import json, hashlib, os
BASE="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes"
def ent(p):
    d=open(os.path.join(BASE,p),'rb').read()
    return {"path": p, "sha256": hashlib.sha256(d).hexdigest(), "bytes": len(d)}
outs=[]
for p in ["root-mathdb-breadth-intake-r348/reserved-ids.json",
          "root-mathdb-breadth-intake-r348/queue.json",
          "root-mathdb-breadth-intake-r348/coverage-delta.json",
          "root-mathdb-breadth-intake-r348/bindings.json",
          "root-mathdb-accepted-exclusions-r304/accepted-exclusions.json",
          "root-mathdb-accepted-exclusions-r304/historical-dispositions.json",
          "pi-mathdb-full-corpus-inventory-r301/manifest.json"]:
    outs.append(ent(p))
for i in range(1,21):
    outs.append(ent(f"pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-{i:04d}.jsonl"))
json.dump(outs, open(os.path.join(BASE,"pi-mathdb-primary-qualified-breadth-r349","bindings.json"),"w"), indent=1)
print("bindings entries:", len(outs))
