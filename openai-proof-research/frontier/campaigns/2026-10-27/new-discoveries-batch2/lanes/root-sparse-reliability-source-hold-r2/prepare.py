from pathlib import Path
import ast
P=Path(__file__).resolve().parent
base='''from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime,runpy
P=Path(__file__).resolve().parent;S=P.parent/'WORKER'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\\n')
m=json.loads((S/'MANIFEST').read_text());rows=json.loads((S/'freeze-before.json').read_text())['files']
ex=m.get('excludes',m.get('exclusions'))
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(ex)==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h,n
def originals():
 for r in rows:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256'],r['original']
originals()
CHECKER
originals()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),original_copy_pairs=len(rows),frozen_files=len(freeze),private_diagnostics='PASS',qualification='Integrity and exact diagnostics only; dispositions recorded separately, no credit.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\\n');print(json.dumps(receipt))
'''
jobs=[('root-sparse-reliability-source-hold-r2','sol-sparse-reliability-source-prior-review-r2','final-manifest.json',"""shutil.copyfile(S/'verify.py',P/'predecessor_checker.py')
j=runpy.run_path(str(P/'predecessor_checker.py'));out=j['check']()
assert out==json.loads((S/'manifest-verification.json').read_text())['diagnostics']
(P/'independent-evidence.json').write_text(json.dumps(out,indent=2)+'\\n')""",'Sparse reliability novelty HOLD retained: actual 2025 arXiv induction uses false Lemma 23(iii), independently checked at n8,m12,x1,rho1/2; this does not clear unread published2025 and Networks2018 bodies. No concrete accessible body route remains; park source/priority gap, no formal or paper investment. Fresh structural r202 assigned.','Preserve sparse reliability predecessor defect and source hold'),('root-totient-deficiency-review-adoption-r1','sol-totient-deficiency-preliminary-review-r1','finalmanifest.json',"""shutil.copyfile(S/'independent_checker.py',P/'independent_checker.py')
with (P/'independent-evidence.json').open('w') as f:subprocess.run([sys.executable,str(P/'independent_checker.py')],stdout=f,check=True)
out=json.loads((P/'independent-evidence.json').read_text());assert out['status']=='PASS' and out['N']==2500""",'Totient normalized-deficiency ordinary MATH PASS retained; root adopts substantive EXCLUDE via complete classical mean, generic squarefree divisor second-moment bound and Cauchy–Schwarz bridge. Mean/limiting-law scope qualified; no exact prior-publication claim, novelty HOLD. No Lean/manuscript or credit. Fresh arithmetic r203 assigned.','Exclude normalized totient candidate via complete classical bridge')]
for root,worker,manifest,checker,intro,msg in jobs:
 d=P.parent/root;d.mkdir(exist_ok=True)
 (d/'verify.py').write_text(base.replace('WORKER',worker).replace('MANIFEST',manifest).replace('CHECKER',checker))
 t=(P.parent/'root-r184-handback/integrate.py').read_text()
 old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
 t=t.replace('sol-fresh-source-discovery-r184',worker).replace(repr(old),repr(intro+' See '+root+'. Counts 9 additional / 39 total, next 40.\n\n')).replace('Preserve uniform quadrature and rearrangement proof gaps',msg)
 (d/'integrate.py').write_text(t)
