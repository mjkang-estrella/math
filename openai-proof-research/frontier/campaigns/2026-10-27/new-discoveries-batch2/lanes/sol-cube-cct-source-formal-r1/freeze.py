from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
items=[]
for lane,names in [('sol-wide-algebra-scout-r222',['PROOF.md','freeze.json','SOURCE_MAP.md','provenance.json']),('sol-cube-cct-preliminary-review-r1',['review.md','freeze.json','before-after.json','primary/published.pdf','primary/published.txt','primary/published.pdf.receipt.json','page-map.json']),('sol-median-temporal-source-formal-r1',['lean_guard.py','pins.json','audit_verify.py','Audit.lean'])]:
 for name in names:
  p=L.parent/lane/name;q=L/'frozen'/lane/name;q.parent.mkdir(parents=True,exist_ok=True)
  h=sha(p);shutil.copyfile(p,q);assert h==sha(p)==sha(q)
  items.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 p=B/name;q=L/'administrative'/name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
(L/'freeze.json').write_text(json.dumps(items,indent=2)+'\n')
shutil.copyfile(L/'frozen/sol-median-temporal-source-formal-r1/lean_guard.py',L/'lean_guard.py')
print('Frozen',len(items),'scientific/workflow inputs; administrative snapshots copied.')
