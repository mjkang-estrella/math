from pathlib import Path
import hashlib,json,shutil,tarfile
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
L=B/'lanes/sol-median-poisson-clock-bridge-formal-r2'
P=B/'lanes/sol-median-temporal-source-formal-r1'
rows=[]
def freeze(p,d):
 d.parent.mkdir(parents=True,exist_ok=True)
 a=p.read_bytes(); d.write_bytes(a); b=p.read_bytes()
 assert a==b==d.read_bytes()
 rows.append(dict(original=str(p),copy=str(d.relative_to(L)),sha256=hashlib.sha256(a).hexdigest()))
for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 freeze(B/n,L/'administrative'/n)
for n in ['SUMMARY.md','source-only.tar.gz','pins.json','run.sh','lean_guard.py','audit_verify.py','Audit.lean','FiniteCore.lean','IntegerLeaf.lean']:
 freeze(P/n,L/'frozen'/n)
freeze(B/'lanes/sol-median-temporal-source-prior-r2/REVIEW.md',L/'frozen/prior-REVIEW.md')
with tarfile.open(L/'frozen/source-only.tar.gz') as t:
 assert all(not m.name.startswith('/') and '..' not in Path(m.name).parts for m in t)
 t.extractall(L/'inherited',filter='data')
(L/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Frozen',len(rows),'inputs; archive extracted privately')
