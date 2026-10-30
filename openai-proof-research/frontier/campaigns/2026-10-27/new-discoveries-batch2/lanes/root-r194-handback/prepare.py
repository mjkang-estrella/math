from pathlib import Path
import ast
P=Path(__file__).resolve().parent
common='''from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-rNUM'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\\n')
m=json.loads((S/'finalmanifest.json').read_text())
if isinstance(m['files'],dict):
 for n,h in m['files'].items():assert sha(S/n)==h,n
 names=set(m['files']);excluded=m['excluded']
else:
 for n,h,z in m['files']:assert sha(S/n)==h and (S/n).stat().st_size==z,n
 names={n for n,h,z in m['files']};excluded=m['explicit_exclusions']
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(excluded)==names
science=json.loads((S/'scientific-freeze.json').read_text())
if isinstance(science,list):
 bindings=[(r['original'],r['copy'],r['sha256'],None) for r in science]
else:
 for n,h,z in science['files']:assert sha(S/n)==h and (S/n).stat().st_size==z
 bindings=json.loads((S/'scientific-input-freeze.json').read_text())['bindings']
def originals():
 for n,c,h,z in bindings:
  for p in [Path(n),S/c]:assert sha(p)==h and (z is None or p.stat().st_size==z),str(p)
originals()
g=S/'guard-binding.json'
if g.exists():
 j=json.loads(g.read_text());assert sha(Path(j['path']))==j['sha256']
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.json').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
originals()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(names),scientific_original_copy_pairs=len(bindings),frozen_files=len(freeze),private_replay='byte-identical',qualification='Exact method controls only; no universal proof or source counterexample.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\\n');print(json.dumps(receipt))
'''
decisions={194:('Matrix-ring recognition remains unresolved.','The source covers even matrix sizes; the conditional composite-size transfer does not prove the missing odd-prime bases. The triangular bimodule ring has the same order and center size as M3(F2), but different commuting-graph degree counts, so it is only a method countermodel. Preserve the unread 2024 predecessor and 2004 attribution qualifications. No nomination or formal investment.'),195:('Higher convex-order separation remains unresolved.','The all-order probability-transform interpolation lemma is missing. The admissible n=4 example defeats direct maximum gluing but has zero moment deficit and admits Z=X; it is not a source counterexample. Translation covers common bounded-below laws only. The 2014 predecessor body remains unread; the new source’s allegation of an incomplete prior proof is attributed, not independently certified. No nomination or formal investment.')}
for num,(title,body) in decisions.items():
 d=P.parent/f'root-r{num}-handback';d.mkdir(exist_ok=True)
 (d/'verify.py').write_text(common.replace('rNUM',f'r{num}'))
 (d/'DECISION.md').write_text(f'# r{num}: zero nomination\n\n{title}\n\n{body}\n\nRoot inspected the reports and checker. The separate root receipt records manifest, scientific original/copy and byte-identical private replay checks. Finite diagnostics establish no universal result. Access and workflow failures remain preserved. Counts remain 9 additional / 39 total, next 40.\n')
 t=(P.parent/'root-r184-handback/integrate.py').read_text()
 old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
 intro=f'r{num}: {title} {body} Root replay and freeze verification pass; see root-r{num}-handback. Fresh replacement r{num+3} assigned. Counts 9 additional / 39 total, next 40.\n\n'
 t=t.replace('sol-fresh-source-discovery-r184',f'sol-fresh-source-discovery-r{num}').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps',f'Preserve r{num} full-scope proof gap and exact method controls')
 (d/'integrate.py').write_text(t)
