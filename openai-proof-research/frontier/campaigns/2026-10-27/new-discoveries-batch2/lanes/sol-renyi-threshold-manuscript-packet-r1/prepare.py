import hashlib,json,shutil,zipfile
from pathlib import Path
R=Path(__file__).resolve().parent
B=R.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
freeze=json.loads((B/'root-renyi-factorial-r116-adoption-r1/renyi-freeze.json').read_text())
for n,h in freeze['files'].items():assert sha(Path(freeze['root'])/n)==h,n
(R/'freeze-before.json').write_text(json.dumps(freeze,indent=2)+'\n')
archive=B/'sol-renyi-deficit-source-formal-r2/component-source.zip'
assert sha(archive)=='ade57965f51e871329be7e62c84b6b8f6c694206b0f20d4bddb1a6bf377ef32d'
P=R/'packet';P.mkdir(exist_ok=True)
with zipfile.ZipFile(archive) as z:
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
 z.extractall(P/'component')
shutil.copy2(archive,P/'component-source.zip')
E=P/'evidence';E.mkdir(exist_ok=True)
paths=['root-renyi-factorial-r116-adoption-r1/DECISION.md','root-renyi-factorial-r116-adoption-r1/ROOT-REPLAY.json','root-renyi-factorial-r116-adoption-r1/renyi-freeze.json','root-renyi-investment-r3/DECISION.md','sol-renyi-threshold-preliminary-review-r1/review.md','sol-renyi-registry-gap-closure-r3/review.md','sol-renyi-threshold-current-prior-review-r2/review.md','sol-renyi-deficit-source-formal-r2/SUMMARY.md','sol-renyi-deficit-source-formal-r2/FINAL-RECEIPT.json','sol-renyi-deficit-source-formal-r2/replay-fresh/replay-receipt.json','sol-fresh-source-discovery-r111/provenance.json']
records={}
for n in paths:
 p=B/n
 if not p.exists():continue
 q=E/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q);records[n]=sha(p)
for n in ['NEXT.md','ledger.json','prior-campaign-context.json']:
 shutil.copy2(B.parent/n,E/n);records['../'+n]=sha(B.parent/n)
for n in ['helper_guard.py']:
 shutil.copy2(B/'sol-edge-irregulator-manuscript-packet-r1/packet'/n,R/n)
assert sha(R/'helper_guard.py')=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
(R/'consulted-before.json').write_text(json.dumps(records,indent=2)+'\n')
print('Freeze verified; immutable source component and bounded evidence copied.')
