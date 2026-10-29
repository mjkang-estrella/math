import hashlib,json,shutil
from pathlib import Path
R=Path(__file__).resolve().parent
B=R.parent
old=B/'sol-renyi-deficit-source-formal-r2'
for d in ['formal','logs','inputs']: (R/d).mkdir(exist_ok=True)
for n in ['guard.py','pins.json','replay_guard.py']:
 shutil.copyfile(old/n,R/n)
audit=(old/'formal/FullAudit.lean').read_text()
start=audit.index('import all Pointwise');end=audit.index('import Lean')
audit=audit[:start]+'import all FactorialProduct\n'+audit[end:]
start=audit.index('  let mods :=');end=audit.index('\n',start)
audit=audit[:start]+'  let mods := #[`FactorialProduct]'+audit[end:]
(R/'formal/FullAudit.lean').write_text(audit)
names={
 'candidate-proof.md':'sol-fresh-source-discovery-r115/PROOF.md',
 'candidate-summary.md':'sol-fresh-source-discovery-r115/SUMMARY.md',
 'source.pdf':'sol-fresh-source-discovery-r115/sources/transversal.pdf',
 'source.txt':'sol-fresh-source-discovery-r115/sources/transversal.txt',
 'source-page.png':'sol-fresh-source-discovery-r115/sources/p1281.png',
 'candidate-provenance.json':'sol-fresh-source-discovery-r115/provenance.json',
 'source-receipts.json':'sol-fresh-source-discovery-r115/source-fetch-receipts.json',
 'preliminary-review.md':'sol-factorial-product-preliminary-review-r1/review.md',
 'prior-review.md':'sol-factorial-product-prior-clearance-r2/review.md',
 'root-adoption.md':'root-renyi-factorial-r116-adoption-r1/DECISION.md',
 'root-preliminary.md':'root-factorial-preliminary-adoption-r1/DECISION.md',
 'root-freeze.json':'root-factorial-product-review-freeze-r1/review-freeze.json',
 'root-check.md':'root-factorial-product-review-freeze-r1/ROOT-CHECK.md',
 'NEXT.md':'../NEXT.md'}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
rows=[]
for n,p in names.items():
 p=(B/p).resolve();h=sha(p);shutil.copyfile(p,R/'inputs'/n)
 assert sha(p)==sha(R/'inputs'/n)==h
 rows.append({'original':str(p),'copy':'inputs/'+n,'sha256':h})
for p in [B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',old/'guard.py',old/'formal/FullAudit.lean',old/'pins.json',old/'replay_guard.py']:
 rows.append({'original':str(p),'sha256':sha(p)})
(R/'frozen-before.json').write_text(json.dumps(rows,indent=2)+'\n')
