from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent; B=L.parent.parent
names={
'sol-quantile-aggregation-full-r1':['PROOF.md','certificate.json','certificate.py','verify_math.py','provenance.md','FAILURES.md'],
'sol-quantile-aggregation-preliminary-review-r1':['review.md'],
'sol-quantile-aggregation-source-prior-r2':['review.md','provenance.md','accepted.txt','accepted.body','source-coverage.json','FAILURES.md']}
rows=[]
for lane,files in names.items():
 for name in files:
  p=L.parent/lane/name; q=L/'frozen'/lane/name; q.parent.mkdir(parents=True,exist_ok=True)
  data=p.read_bytes(); h=hashlib.sha256(data).hexdigest();q.write_bytes(data)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
  rows.append({'original':str(p),'copy':str(q.relative_to(L)),'sha256_before':h})
(L/'administrative').mkdir(exist_ok=True)
for name in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
 shutil.copyfile(B/name,L/'administrative'/name)
(L/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/name).read_text())
 print(name, 'keys',list(d))
 if name=='ledger.json':print({k:d[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']})
 print(json.dumps(d,indent=2)[:0])
print('Frozen',len(rows),'scientific files before reading')
