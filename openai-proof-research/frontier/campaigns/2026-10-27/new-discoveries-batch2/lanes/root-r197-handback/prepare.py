from pathlib import Path
import ast
P=Path(__file__).resolve().parent
verifier='''from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-rNUM';R=S.parents[5]
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\\n')
m=json.loads((S/'finalmanifest.json').read_text());excluded=m.get('excludes',m.get('exclusions'))
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(excluded)==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h,n
if S.name.endswith('197'):
 rows=json.loads((S/'input-bindings.json').read_text())+json.loads((S/'scientific-input-freeze.json').read_text())['bindings']
else:
 rows=[(r['original'],r['copy'],r['sha256'],None) for r in json.loads((S/'scientific-freeze.json').read_text())]
def originals():
 for n,c,h,z in rows:
  a=Path(n);a=a if a.is_absolute() else R/a
  for p in [a,S/c]:assert sha(p)==h and (z is None or p.stat().st_size==z),str(p)
originals();shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.json').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,check=True)
if S.name.endswith('197'):
 a=json.loads((P/'checks.json').read_text());b=json.loads((S/'checks.json').read_text());a.pop('utc');b.pop('utc');assert a==b
 replay='scientific JSON identical excluding actual run UTC'
else:
 assert (P/'checks.json').read_bytes()==(S/'checks-final.json').read_bytes();replay='byte-identical'
originals()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),scientific_original_copy_pairs=len(rows),frozen_files=len(freeze),private_replay=replay,qualification='Method diagnostics only; universal source endpoint remains unresolved. Inherited failures preserved.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\\n');print(json.dumps(receipt))
'''
decisions={197:('Hu–Liu Question 4.4 remains unresolved.','Completion doubling and strong-m results do not supply anisotropy detection over all target rational-function fields. The universal Pfister examples obstruct a fixed coordinate completion, not the existential detection lemma or source claim. The published 2026 predecessor comparison remains unread/HOLD.',199),198:('The full Robin fixed-perimeter question remains unresolved.','The phase trial space has a positive shifted-energy diagonal for noncircular convex obstacles; this defeats that method, not the spectral conjecture. A uniform conformal weighted variational bound and the nonconvex scope remain open. Coverage is excluded by the actual public Fano refutation. Concurrent r196 PROOF change was preserved with old and refreshed copies; only the refreshed final freeze is verified, with no retroactive initial-freeze PASS.',200)}
for num,(title,body,new) in decisions.items():
 d=P.parent/f'root-r{num}-handback';d.mkdir(exist_ok=True)
 (d/'verify.py').write_text(verifier.replace('rNUM',f'r{num}'))
 (d/'DECISION.md').write_text(f'# r{num}: zero nomination\n\n{title}\n\n{body}\n\nRoot inspected reports and checkers. The separate receipt records private replay and original/copy/manifest checks. Finite controls prove no universal result. No formal investment or credit; counts remain 9 additional / 39 total, next 40.\n')
 t=(P.parent/'root-r184-handback/integrate.py').read_text()
 old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
 intro=f'r{num}: {title} {body} Root replay and final integrity checks pass. See root-r{num}-handback; fresh replacement r{new} assigned. Counts 9 additional / 39 total, next 40.\n\n'
 t=t.replace('sol-fresh-source-discovery-r184',f'sol-fresh-source-discovery-r{num}').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps',f'Preserve r{num} universal gap and checked method obstructions')
 (d/'integrate.py').write_text(t)
