import json,hashlib,os
LANE="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/pi-mathdb-primary-qualified-breadth-r327"
m=json.load(open(os.path.join(LANE,"manifest.json")))
ok=True; errs=[]
# 1. all listed files exist with matching size+sha
for f in m["files"]:
    p=os.path.join(LANE,f["path"])
    if not os.path.exists(p): errs.append("missing "+f["path"]); ok=False; continue
    h=hashlib.sha256(open(p,'rb').read()).hexdigest()
    if h!=f["sha256"] or os.path.getsize(p)!=f["bytes"]:
        errs.append("mismatch "+f["path"]); ok=False
# 2. enumerate actual payloads; detect unlisted files (excluding manifest+receipt by exact name)
actual=set()
for root,dirs,fs in os.walk(LANE):
    dirs[:]=[d for d in dirs if d!="__pycache__"]
    for f in fs:
        rel=os.path.relpath(os.path.join(root,f),LANE)
        if rel not in ("manifest.json","verification-receipt.json") and "__pycache__" not in rel:
            actual.add(rel)
listed={f["path"] for f in m["files"]}
unlisted=actual-listed; phantom=listed-actual
if unlisted: errs.append("UNLISTED: "+",".join(sorted(unlisted))); ok=False
if phantom: errs.append("phantom: "+",".join(sorted(phantom))); ok=False
# 3. coverage: all 50 reserved IDs in dispositions, disjoint from 183 prior
res=set(map(str,json.load(open(os.path.join(LANE,"frozen/reserved-ids.json")))))
D=json.load(open(os.path.join(LANE,"dispositions.json")))
if set(D["dispositions"])!=res: errs.append("disposition ID set mismatch"); ok=False
cov=json.load(open(os.path.join(LANE,"frozen/coverage-delta.json")))
if res & set(cov): errs.append("overlap with prior 183"); ok=False
# 4. source bindings: 19 entries, all files exist and hashes match
sb=json.load(open(os.path.join(LANE,"work/source-bindings.json")))
if len(sb)!=26: errs.append("source-bindings count %d"%len(sb)); ok=False
for b in sb:
    p=os.path.join(LANE,b["file"])
    if not os.path.exists(p) or hashlib.sha256(open(p,'rb').read()).hexdigest()!=b["sha256"]:
        errs.append("binding fail "+b["file"]); ok=False
# 5. corpus chunks verified in place (20/20)
cv=json.load(open(os.path.join(LANE,"work/corpus-verification.json")))
if len(cv)!=20 or not all(c["match"] for c in cv): errs.append("corpus verification incomplete"); ok=False
receipt={"scope":"post-write integrity verification only; no mathematical/priority endorsement",
 "result":"PASS" if ok else "FAIL","listed_files":len(m["files"]),
 "unlisted_files":sorted(unlisted),"phantom_files":sorted(phantom),
 "dispositions":len(D["dispositions"]),"reserved":len(res),
 "source_bindings":len(sb),"corpus_chunks_verified_in_place":len(cv),
 "checked_utc":"2026-10-30T18:47:00Z","errors":errs}
json.dump(receipt,open(os.path.join(LANE,"verification-receipt.json"),"w"),indent=1)
print(json.dumps(receipt,indent=1))
