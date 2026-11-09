from pathlib import Path
import json,hashlib,shutil,tarfile
L=Path(__file__).resolve().parent
rows=json.loads((L/'freeze.json').read_text())
def freeze(f,d):
 b=f.read_bytes();h=hashlib.sha256(b).hexdigest();d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(b)
 assert hashlib.sha256(f.read_bytes()).hexdigest()==h==hashlib.sha256(d.read_bytes()).hexdigest()
 rows.append(dict(original=str(f),copy=str(d.relative_to(L)),sha256=h))
C=L.parent/'sol-floor-sums-certificate-r2'
freeze(C/'dag.jsonl',L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl')
for n in ['all-m-query.smt2','z3-proof.sexpr']:
 freeze(C/'frozen'/n,L/'frozen/primary'/n)
R=L.parent/'sol-floor-sums-certificate-formal-r2'
for f in sorted((R/'generated').glob('th_lemma_*.lean')):
 freeze(f,L/'generated'/f.name)
for n in ['Reduction.lean','Symmetry.lean','Source.lean','Expansion.lean','Audit.lean','verify_audit.py','pins.json','lean_guard.py']:
 shutil.copyfile(L/'frozen/sol-floor-sums-certificate-formal-r2'/n,L/n)
(L/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
N=[json.loads(s) for s in (L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl').open()]
def h(i):
 x=N[i];return x.get('atom') or h(x['args'][0])
for op in ['lemma','intro-def','apply-def','rewrite','monotonicity','asserted']:
 print(op,[(i,d) for i,d in enumerate(N) if 'args'in d and h(i)==op][:3])
