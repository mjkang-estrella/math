from pathlib import Path
import hashlib,json,re,subprocess,sys,zipfile
R=Path(__file__).resolve().parent; D=Path(sys.argv[1]).resolve();assert not D.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(R/'source-only.zip')=='3023e47a5994d0f4e0571c8fdf89b2b34a8ffb6f585636cd1eaf01026df1c055'
with zipfile.ZipFile(R/'source-only.zip') as z:
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist());z.extractall(D)
manifest=json.loads((D/'manifest.json').read_text())
def check():
 for n,h in manifest.items():assert sha(D/n)==h,n
 for row in json.loads((D/'frozen-before.json').read_text()):
  if 'copy' in row:assert sha(D/row['copy'])==row['sha256']
 for row in json.loads((D/'dependency-hashes.json').read_text()):assert sha(Path(row['path']))==row['sha256']
check();pins=json.loads((D/'pins.json').read_text())
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',(D/'formal/FactorialProduct.lean').read_text())
assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
# Reuse the original exact pin validator, stopping before historical-original checks.
src=(D/'verify.py').read_text().split("rows=json.loads((R/'frozen-before.json').read_text())")[0]
exec(compile(src,str(D/'verify.py'),'exec'),{'__file__':str(D/'verify.py')})
assert not any(p.name.endswith(('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig')) for p in D.rglob('*'))
(D/'logs').mkdir(exist_ok=True)
for m in ['FactorialProduct','FullAudit']:
 r=subprocess.run([sys.executable,str(D/'guard.py'),m],capture_output=True,text=True)
 print(r.stdout,flush=True);assert r.returncode==0,r.stderr
assert (D/'logs/FactorialProduct.log').stat().st_size==0
log=(D/'logs/FullAudit.log').read_text()
rows=re.findall(r'^AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS \[([^\]]*)\]\nFLAGS unsafe=(\w+) partial=(\w+) axiom=(\w+)$',log,re.M|re.S)
assert len(rows)==int(re.search(r'AUDIT_TOTAL (\d+)',log)[1])==31
assert len({r[1] for r in rows})==31 and {r[0] for r in rows}=={'FactorialProduct'}
for mod,n,t,axs,u,p,a in rows:
 assert t and set(re.findall(r'[\w.]+',axs))<={'propext','Classical.choice','Quot.sound'}
 assert (u,p,a)==('false','false','false')
# Exhaustive actual upstream artifact inventory, including private/server companions.
actual=set()
for mod in (D/'formal/dependencies.txt').read_text().splitlines():
 if mod=='FactorialProduct':continue
 rel=Path(*mod.split('.')).with_suffix('.olean')
 hits=[Path(p['path'])/'.lake/build/lib/lean'/rel for p in pins['packages']];hits=[p for p in hits if p.is_file()]
 if hits:
  assert len(hits)==1
  for s in ['', '.private','.server']:
   p=Path(str(hits[0])+s)
   if p.is_file():actual.add(str(p))
 else:assert (Path(pins['lean_binary']).parent.parent/'lib/lean'/rel).is_file()
assert actual=={p['path'] for p in json.loads((D/'dependency-hashes.json').read_text())}
check()
(D/'portable-receipt.json').write_text(json.dumps({'status':'PORTABLE_SOURCE_ONLY_PASS','actual_declarations':31,
 'initial_own_compiled_artifacts':0,'mathematical_compilelog_bytes':0,'historical_originals_required':False,
 'audit_sha256':sha(D/'logs/FullAudit.log'),'mathematical_source_sha256':sha(D/'formal/FactorialProduct.lean')},indent=2)+'\n')
