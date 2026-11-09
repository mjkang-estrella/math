import json, os
ROOT="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes"
LANE=ROOT+"/pi-mathdb-primary-first-breadth-r314"
CORPUS=ROOT+"/pi-mathdb-full-corpus-inventory-r301/corpus"
bind=json.load(open(LANE+"/source-bindings.json"))
want=set(bind["reserved_ids"])
recs={}
for fn in sorted(os.listdir(CORPUS)):
    if not fn.endswith(".jsonl"): continue
    with open(os.path.join(CORPUS,fn)) as f:
        for line in f:
            if line.lstrip().startswith("{"):
                try: rec=json.loads(line)
                except Exception: continue
                if rec.get("mathdb_id") in want:
                    recs[rec["mathdb_id"]]=rec
out=[]
for i in bind["reserved_ids"]:
    r=recs[i]
    out.append({"mathdb_id":i,"chunk":bind["id_to_chunk"][str(i)][0],
      "title":r.get("title"),"status":r.get("status"),"post_type":r.get("post_type"),
      "statement":r.get("statement"),"sources":r.get("sources"),"tags":r.get("tags"),
      "solutions":r.get("solutions"),"statement_completeness":r.get("statement_completeness"),
      "importance":r.get("importance")})
json.dump(out,open(LANE+"/statements-raw.json","w"),indent=1)
# compact readable digest
with open(LANE+"/statements-digest.txt","w") as f:
    for o in out:
        st=(o["statement"] or "")[:2600]
        sol=o["solutions"]
        nsol=len(sol) if isinstance(sol,list) else sol
        f.write(f"=== {o['mathdb_id']} [{o['status']}/{o['post_type']}] chunk={o['chunk']} sols={nsol} tags={o['tags']}\nTITLE: {o['title']}\nSTMT: {st}\nSOURCES: {json.dumps(o['sources'])[:500]}\n\n")
print("wrote", len(out))
