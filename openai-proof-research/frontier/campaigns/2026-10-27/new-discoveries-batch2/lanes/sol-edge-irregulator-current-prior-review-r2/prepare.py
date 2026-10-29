from pathlib import Path
import hashlib,json,shutil,datetime
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'); O=B/'lanes/sol-edge-irregulator-current-prior-review-r2'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=B/'lanes/root-edge-irregulator-review-freeze-r1/review-freeze.json'; F=json.loads(f.read_text()); S=Path(F['source_lane'])
checks={k:sha(S/k)==h for k,h in F['files'].items()}
for k in F['files']:
 d=O/'candidate'/k;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(S/k,d)
items=[(B/'AGENTS.md','context/B-AGENTS.md'),(B/'ledger.json','context/ledger.json'),(B/'prior-campaign-context.json','context/prior-campaign-context.json'),(B.parents[3]/'AGENTS.md','context/ancestor-AGENTS.md'),(f,'context/review-freeze.json')]
R=B/'lanes/root-edge-irregulator-current-prior-r1'
for name in ['CURRENT-REGISTRIES.json','omega-tree.txt','openai-tree.txt','openai-CONTENTS.md','record.py','record.log','record-guard.log']:items.append((R/name,'registry/'+name))
for p in (R/'current-bodies').rglob('*'):
 if p.is_file():items.append((p,'registry/current-bodies/'+str(p.relative_to(R/'current-bodies'))))
P=B/'lanes/sol-edge-irregulator-preliminary-review-r1'
for name in ['review.md','review-freeze.json','freeze-summary.txt','live/http.json','live-web-results.json','live-web-details.json']:items.append((P/name,'preliminary/'+name))
receipts=[]
for p,d in items:
 dest=O/d;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest);receipts.append({'original':str(p),'copy':d,'sha256':sha(dest)})
(O/'input-copies.json').write_text(json.dumps(receipts,indent=2))
(O/'freeze-before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':checks,'all_pass':all(checks.values()),'count':len(checks)},indent=2))
print('Freeze',len(checks),all(checks.values()));print('Bodies',*[str(p.relative_to(O)) for p in (O/'registry/current-bodies').rglob('*') if p.is_file()],sep='\n')
