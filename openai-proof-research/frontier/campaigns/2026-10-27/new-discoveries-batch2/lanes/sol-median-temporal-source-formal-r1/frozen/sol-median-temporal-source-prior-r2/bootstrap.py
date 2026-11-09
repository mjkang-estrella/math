from pathlib import Path
import hashlib,json,datetime,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
C=L.parent/'sol-median-dynamics-breadth-depth-r1'
P=L.parent/'sol-median-temporal-preliminary-review-r1'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
selected=[C/x for x in ['PROOF.md','SUMMARY.md','FAILURES.md','source-map.json','provenance.json','history-screen.json','certificate-results.json','freeze.json']]+[P/'REVIEW.md',P/'independent-results.json',P/'current-access.json']+[C/'frozen'/x for x in ['1911.08613v2.pdf','1911.08613v2.txt','pinned-upstream.json','pinned-CONTENTS.md','pinned-preprints-tree.json','median-current.xml','median-companions.xml','majority-convexity.xml','r221--history-screen.json']]
for i,p in enumerate(selected):
 q=L/'freeze'/('%02d--'%i+p.name);q.parent.mkdir(exist_ok=True)
 h=sha(p);shutil.copyfile(p,q);assert sha(p)==sha(q)==h
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h))
(L/'binding-before.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=rows),indent=2))
(L/'administrative').mkdir(exist_ok=True)
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json']:
 shutil.copyfile(p,L/'administrative'/p.name)
print('scientific freeze',len(rows))
for p in [B/'ledger.json',B/'prior-campaign-context.json']:
 d=json.loads(p.read_text());print(p.name, 'top-level keys',list(d));print('counts',{k:v for k,v in d.items() if 'count' in k or 'next_' in k})
