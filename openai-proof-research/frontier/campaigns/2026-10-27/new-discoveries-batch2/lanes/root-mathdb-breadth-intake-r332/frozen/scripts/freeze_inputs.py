import json,hashlib,os,shutil
BASE="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2"
LANE=BASE+"/lanes/pi-mathdb-primary-qualified-breadth-r327"
# sources to freeze (originals elsewhere), copied and bound BEFORE content read
SRCS={
 "reserved-ids.json": BASE+"/lanes/root-mathdb-breadth-intake-r326/reserved-ids.json",
 "queue.json": BASE+"/lanes/root-mathdb-breadth-intake-r326/queue.json",
 "coverage-delta.json": BASE+"/lanes/root-mathdb-breadth-intake-r326/coverage-delta.json",
 "QUALIFICATIONS.md": BASE+"/lanes/root-mathdb-breadth-intake-r326/QUALIFICATIONS.md",
 "r301-manifest.json": BASE+"/lanes/pi-mathdb-full-corpus-inventory-r301/manifest.json",
 "r304-accepted-exclusions.json": BASE+"/lanes/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json",
 "r304-historical-dispositions.json": BASE+"/lanes/root-mathdb-accepted-exclusions-r304/historical-dispositions.json",
 "r320-dispositions.json": BASE+"/lanes/pi-mathdb-primary-qualified-breadth-r320/dispositions.json",
 "r320-proposals.json": BASE+"/lanes/pi-mathdb-primary-qualified-breadth-r320/proposals.json",
 "r322-DECISION.md": BASE+"/lanes/root-mathdb-clt-intake-r322/DECISION.md",
 "r324-DECISION.md": BASE+"/lanes/root-mathdb-hermite-intake-r324/DECISION.md",
}
def sha(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): h.update(b)
    return h.hexdigest()
out=[]
for name,src in SRCS.items():
    dst=os.path.join(LANE,"frozen",name)
    shutil.copyfile(src,dst)
    a,b=sha(src),sha(dst)
    assert a==b
    out.append({"path":"frozen/"+name,"bytes":os.path.getsize(dst),"sha256":a})
json.dump(out,open(os.path.join(LANE,"work","frozen-inputs.json"),"w"),indent=1)
print(json.dumps(out,indent=1))
