"""Fresh source-only replay; no Lake invocation and no upstream modifications."""
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,resource.RLIM_INFINITY))
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,)*2)
import hashlib,json,os,re,signal,subprocess,sys,zipfile
from pathlib import Path
signal.alarm(230)
ALLOW={'propext','Classical.choice','Quot.sound'}
MODULES=['Crossing','Transfer','Cases']
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
def revision(p):
 g=p/'.git'
 if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 h=(g/'HEAD').read_text().strip()
 if h.startswith('ref: '):
  r=h[5:];f=g/r
  h=f.read_text().strip() if f.exists() else next(x.split()[0] for x in (g/'packed-refs').read_text().splitlines() if x.endswith(' '+r))
 return h
packet=Path(sys.argv[1]).resolve();dest=Path(sys.argv[2]).resolve();assert not dest.exists()
with zipfile.ZipFile(packet) as z:
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
 assert not any(n.endswith(('.olean','.ilean','.ir','.o','.so')) for n in z.namelist())
 z.extractall(dest)
(dest/'logs').mkdir()
manifest=json.loads((dest/'manifest.json').read_text())
for n,h in manifest.items():assert sha(dest/n)==h,n
pins=json.loads((dest/'pins.json').read_text());assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
assert len(pins['packages'])==9
for p in pins['packages']:assert revision(Path(p['path']))==p['rev'],p['name']
for p in json.loads((dest/'dependency-hashes.json').read_text()):assert sha(Path(p['path']))==p['sha256'],p['path']
assert not list(dest.rglob('*.olean'))
for m in MODULES:
 src=(dest/'formal'/f'{m}.lean').read_text()
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',src),m
steps=[]
for m in MODULES+['OriginAudit']:
 print('BUILD',m,flush=True)
 r=subprocess.run([sys.executable,str(dest/'guard.py'),m],capture_output=True,text=True)
 print(r.stdout,flush=True);assert r.returncode==0,r.stderr
 step=json.loads((dest/'logs'/f'{m}.json').read_text());assert not step['kill'] and step['exit']==0
 assert step['peak_group_rss_kib']<=2800*1024;steps.append(step)
 if m!='OriginAudit':assert (dest/'logs'/f'{m}.log').stat().st_size==0
log=(dest/'logs/OriginAudit.log').read_text()
rows=re.findall(r'^AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS \[([^\]]*)\]\nFLAGS unsafe=(\w+) partial=(\w+) axiom=(\w+)$',log,re.M|re.S)
# Restrict the TYPE block match at each next AUDIT marker; no duplicate declarations.
assert len(rows)==int(re.search(r'AUDIT_TOTAL (\d+)',log)[1])
assert len({r[1] for r in rows})==len(rows)
assert {r[0] for r in rows}==set(MODULES)
for mod,name,typ,axs,u,p,a in rows:
 assert typ and set(re.findall(r'[\w.]+',axs))<=ALLOW
 assert (u,p,a)==('false','false','false')
for n,h in manifest.items():assert sha(dest/n)==h,n
result={'status':'PASS','scope':'Generic Wronskian one-crossing and unimodality transfer; conditional analytic premises retained',
 'archive_sha256':sha(packet),'initial_own_prebuilt_artifacts':0,'proof_modules':MODULES,
 'transitive_safety_closure_count':int(re.search(r'SAFETY_CLOSURE (\d+)',log)[1]),'declaration_count':len(rows),'actual_types_and_origins_and_flags_and_transitive_axiom_closure':True,
 'audit_inventory_crosscheck':'env.constants/getModuleIdxFor? against moduleData.constNames',
 'axiom_union':sorted(set().union(*(set(re.findall(r'[\w.]+',r[3])) for r in rows))),
 'all_unsafe_partial_axiom_flags_false':True,'pins':pins,'steps':steps,
 'process_group_rss_ceiling_kib':2800*1024,'rss_sampling_target_seconds':.045,
 'sampled_transients_limit':'Unsampled transients cannot be excluded.',
 'declarations':[{'origin':r[0],'name':r[1],'actual_type':r[2],'axioms':re.findall(r'[\w.]+',r[3]),'unsafe':False,'partial':False,'axiom':False} for r in rows]}
(dest/'replay-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(rows),'declarations')
