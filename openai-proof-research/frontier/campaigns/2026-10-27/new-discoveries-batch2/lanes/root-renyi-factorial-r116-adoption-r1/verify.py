import hashlib,json,datetime
from pathlib import Path
from fractions import Fraction as F
root=Path(__file__).resolve().parent
lanes=root.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536): h.update(b)
 return h.hexdigest()
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'credit':0,'counts':[8,38]}
r=lanes/'sol-fresh-source-discovery-r116'
rows=[json.loads(s) for s in (r/'manifest.jsonl').read_text().splitlines()]
for q in rows: assert sha(r/q['path'])==q['sha256'],q['path']
phi=lambda x:min(x*x,x)
# All selected inverse arguments are >=1, so the inverse is exactly the argument.
px=(phi(F(1,2))+phi(F(100)))/10
py=phi(F(10))/10
pxy=(phi(F(21,2))+phi(F(100)))/10
assert min(px,py,pxy)>=1 and pxy-px-py==F(1,40)
assert phi(F(1))-(phi(F(3,4))+phi(F(5,4)))/2==F(3,32)
out['r116']={'manifest_entries':len(rows),'status':'UNRESOLVED','exact_route_defect':str(pxy-px-py),'source_counterexample':False}
r=lanes/'sol-factorial-product-prior-clearance-r2'
rows=json.loads((r/'final-manifest.json').read_text())['files']
for q in rows: assert sha(r/q['path'])==q['sha256'],q['path']
out['factorial_prior']={'manifest_entries':len(rows),'review_sha256':sha(r/'review.md'),'status':'CLEAR_BOUNDED','substantive':'SCOPED_PASS_WITH_COUNTING_OBJECTION','adjacent_unread':'Jevtic DOI 10.1137/S0895480194265623'}
r=lanes/'sol-renyi-deficit-source-formal-r2'
manifest=json.loads((r/'manifest.json').read_text())
for n,h in manifest.items(): assert sha(r/n)==h,n
receipt=json.loads((r/'FINAL-RECEIPT.json').read_text())
assert sha(r/'component-source.zip')==receipt['archive']['sha256']
assert sha(r/receipt['fresh_replay_receipt'])==receipt['fresh_replay_receipt_sha256']
freeze={n:sha(r/n) for n in list(manifest)+['manifest.json','component-source.zip','FINAL-RECEIPT.json','SUMMARY.md','replay-fresh/replay-receipt.json']}
(root/'renyi-freeze.json').write_text(json.dumps({'root':str(r),'files':freeze},indent=2)+'\n')
out['renyi']={'manifest_entries':len(manifest),'archive_sha256':receipt['archive']['sha256'],'worker_audit_count':104,'root_replay':'PENDING'}
(root/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
