import hashlib,json,re,subprocess,sys,zipfile
from pathlib import Path
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
archive=Path(sys.argv[1]).resolve();dest=Path(sys.argv[2]).resolve();assert not dest.exists()
with zipfile.ZipFile(archive) as z:
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
 assert not any(n.endswith(('.olean','.ilean','.ir','.o','.so')) for n in z.namelist())
 z.extractall(dest)
manifest=json.loads((dest/'manifest.json').read_text())
for n,h in manifest.items():assert sha(dest/n)==h,n
for m in ['FactorialProduct']:
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',
  (dest/'formal'/f'{m}.lean').read_text()),m
for p in json.loads((dest/'dependency-hashes.json').read_text()):assert sha(Path(p['path']))==p['sha256']
helper=next(Path(r['original']) for r in json.loads((dest/'frozen-before.json').read_text())
 if Path(r['original']).name=='helper_guard.py')
assert helper.name=='helper_guard.py'
r=subprocess.run([sys.executable,str(helper),sys.executable,str(dest/'verify.py')],capture_output=True,text=True)
assert r.returncode==0,r.stderr
(dest/'pins-and-inputs.json').write_text(r.stdout)
(dest/'logs').mkdir(exist_ok=True)
assert not list(dest.rglob('*.olean'))
steps=[]
for m in ['FactorialProduct','FullAudit']:
 print('BUILD',m,flush=True)
 r=subprocess.run([sys.executable,str(dest/'guard.py'),m],capture_output=True,text=True)
 print(r.stdout,flush=True);assert r.returncode==0,r.stderr
 steps.append(json.loads((dest/'logs'/f'{m}.json').read_text()))
 if m!='FullAudit':assert (dest/'logs'/f'{m}.log').stat().st_size==0
log=(dest/'logs/FullAudit.log').read_text()
pins=json.loads((dest/'pins.json').read_text());actual=set()
for mod in (dest/'formal/dependencies.txt').read_text().splitlines():
 if mod=='FactorialProduct':continue
 rel=Path(*mod.split('.')).with_suffix('.olean')
 hits=[Path(p['path'])/'.lake/build/lib/lean'/rel for p in pins['packages']]
 hits=[p for p in hits if p.is_file()]
 if hits:
  assert len(hits)==1
  for suffix in ['', '.private', '.server']:
   p=Path(str(hits[0])+suffix)
   if p.is_file():actual.add(str(p))
 else:assert (Path(pins['lean_binary']).parent.parent/'lib/lean'/rel).is_file(),mod
assert actual=={p['path'] for p in json.loads((dest/'dependency-hashes.json').read_text())}
rows=re.findall(r'^AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS \[([^\]]*)\]\nFLAGS unsafe=(\w+) partial=(\w+) axiom=(\w+)$',log,re.M|re.S)
assert len(rows)==int(re.search(r'AUDIT_TOTAL (\d+)',log)[1])
assert len({r[1] for r in rows})==len(rows) and {r[0] for r in rows}=={'FactorialProduct'}
for mod,name,typ,axs,u,p,a in rows:
 assert typ and set(re.findall(r'[\w.]+',axs))<={'propext','Classical.choice','Quot.sound'}
 assert (u,p,a)==('false','false','false')
for n,h in manifest.items():assert sha(dest/n)==h,n
r=subprocess.run([sys.executable,str(helper),sys.executable,str(dest/'verify.py')],capture_output=True,text=True)
assert r.returncode==0,r.stderr
result={'status':'LITERAL_GAMMA_SOURCE_REFUTATION_PASS','full_target_proved':True,
 'archive_sha256':sha(archive),'initial_own_prebuilt_artifacts':0,'mathematical_compilelog_bytes':0,
 'warningsAsErrors':True,'declaration_count':len(rows),'steps':steps,
 'declarations':[{'origin':m,'name':n,'actual_type':t,'transitive_axioms':re.findall(r'[\w.]+',axs),
 'unsafe':False,'partial':False,'axiom':False} for m,n,t,axs,u,p,a in rows]}
(dest/'replay-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print('LITERAL GAMMA SOURCE REFUTATION PASS',len(rows),'declarations')
