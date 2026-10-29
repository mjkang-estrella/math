from pathlib import Path
import json,hashlib,shutil
L=Path(__file__).resolve().parent; B=L.parent.parent
f=json.loads((L.parent/'root-mmpp-survival-review-freeze-r1/review-freeze.json').read_text()); src=Path(f['source_lane']); out={}
for p,h in f['files'].items():
 b=(src/p).read_bytes(); assert hashlib.sha256(b).hexdigest()==h,p
 q=L/'copy'/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b);out[p]=h
(L/'before.json').write_text(json.dumps({'verified':len(out),'files':out},indent=2))
shutil.copyfile(L.parent/'root-mmpp-survival-review-freeze-r1/review-freeze.json',L/'review-freeze.json')
for p in ['AGENTS.md','NEXT.md','ledger.json','prior-campaign-context.json']:
 q=L/'context'/p;q.parent.mkdir(exist_ok=True);shutil.copyfile(B/p,q)
for lane in ['sol-mmpp-historical-prior-review-r2','sol-mmpp-survival-preliminary-review-r1']:
 for p in ['review.md','provenance.json','http.json']:
  q=L/'context'/lane/p;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(L.parent/lane/p,q)
for p in ['last-penrose-book.txt','baccelli-blaszczyszyn.txt','asmussen-koole.txt','withdrawn-v1.txt','omega-new-body.md','omega-compare.json','omega-head.json','openai-head.json']:
 q=L/'evidence'/p;q.parent.mkdir(exist_ok=True);shutil.copyfile(L.parent/'sol-mmpp-historical-prior-review-r2/sources'/p,q)
print('55 originals verified and copied')
