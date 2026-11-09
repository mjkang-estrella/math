import json,pathlib,hashlib
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r649'
ids={r['mathdb_id'] for r in json.loads((I/'queue-r650.json').read_text())};out=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('mathdb_id',r.get('id')) in ids:
   out.append({'chunk':str(p),'line':n,'record':r,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
(D/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for r in out:print(json.dumps(r,ensure_ascii=False))
print('RESERVATION', (I/'reserved-ids-r650.json').read_text())
print('ADJUDICATION', (I/'adjudications.json').read_text())
print('HYPOTHESES', (I/'hypothesis-queue.json').read_text())
for f in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 v=json.loads((L/f).read_text());print('EXCLUSIONS',f,json.dumps(v,ensure_ascii=False)[:1800])
print((L/'root-mathdb-cayley-review-intake-r363/DECISION.md').read_text())
