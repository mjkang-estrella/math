from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
B=L.parent.parent
items={
'sol-quantile-certificate-compression-r1':['PROOF.md','coupling20.json','exact-check.json','provenance.md','FAILURES.md'],
'sol-quantile-aggregation-full-r1':['PROOF.md','certificate.json','provenance.md'],
'sol-quantile-aggregation-source-prior-r2':['accepted.body','accepted.txt','review.md','provenance.md','FAILURES.md','source-coverage.json','registry-head-bindings.json'],
'sol-quantile-aggregation-preliminary-review-r1':['review.md','provenance.md','FAILURES.md']}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for lane,names in items.items():
 for name in names:
  p=B/'lanes'/lane/name;q=L/'frozen'/lane/name
  before=sha(p);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
  after=sha(p);copy=sha(q);assert before==after==copy
  rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=before,original_after=after,copy_after=copy))
admin=[]
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']:
 q=L/'administrative'/('ancestor-AGENTS.md' if p==B.parents[3]/'AGENTS.md' else p.name)
 q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes());admin.append(dict(original=str(p),snapshot=str(q.relative_to(L)),sha256=sha(q)))
(L/'freeze.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scientific=rows,administrative_snapshots=admin),indent=2)+'\n')
print('Frozen',len(rows),'scientific files; administrative snapshots',len(admin))
