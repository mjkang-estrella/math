from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent; b=json.loads((L/'input-bindings.json').read_text()); ids=set(json.loads((L/'intake-check.json').read_text())['assigned_ids']); out=[]
for p in b['corpus_chunks']:
 for n,line in enumerate(open(p),1):
  r=json.loads(line)
  if int(r.get('mathdb_id',r.get('id',-1))) in ids:
   out.append(dict(record=r,corpus_path=p,line=n))
assert len(out)==50
(L/'statements.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print('record keys',list(out[0]['record']))
for r in out: print(json.dumps(r['record'],ensure_ascii=False))
