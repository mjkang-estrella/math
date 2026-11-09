from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[2]
files=[
 B/'lanes/sol-zeckendorf-mixing-obstruction-r284/PROOF.md',
 B/'lanes/sol-zeckendorf-mixing-preliminary-review-r1/review.md',
 B/'lanes/sol-zeckendorf-mixing-source-prior-review-r2/review.md',
 B/'lanes/sol-zeckendorf-mixing-source-prior-review-r2/provenance.json',
 B/'lanes/sol-zeckendorf-mixing-formal-feasibility-r2/AUDIT.md',
 B/'lanes/sol-zeckendorf-mixing-formal-feasibility-r2/declaration-references.json',
 B/'lanes/root-zeckendorf-review-disposition-r2/FINITE-CONCENTRATION.md',
 B/'lanes/sol-jacobi-source-claim-formal-r1/formal/guard.py',
 B/'lanes/sol-jacobi-source-claim-formal-r1/scripts/replay.py',
]
files += list((B/'lanes/sol-zeckendorf-mixing-source-prior-review-r2').glob('sources/*.txt'))
files += list((B/'lanes/sol-zeckendorf-mixing-formal-feasibility-r2/cached').glob('*NormalForm*.lean'))
files += list((B/'lanes/sol-zeckendorf-mixing-formal-feasibility-r2/cached').glob('*ResidualMachine*.lean'))
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
files += [P/'.lake/packages/mathlib/Mathlib/Data/Nat/Fib/Basic.lean',P/'.lake/packages/mathlib/Mathlib/Data/Nat/Fib/Zeckendorf.lean']
rows=[]
for i,p in enumerate(files):
 if not p.is_file():
  print('MISSING',p);continue
 d=p.read_bytes(); h=hashlib.sha256(d).hexdigest()
 q=L/'frozen'/f'{i:02d}-{p.name}';q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(d)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h))
(L/'source-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'lanes/root-zeckendorf-formal-investment-r1/STATUS.md',P/'lake-manifest.json',P/'lean-toolchain']:
 q=L/'administrative'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes())
print(json.dumps(rows,indent=2))
