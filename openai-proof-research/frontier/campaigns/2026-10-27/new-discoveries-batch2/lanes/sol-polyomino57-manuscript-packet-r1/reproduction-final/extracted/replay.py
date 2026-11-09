"""Serial fresh replay; invoke from anywhere. Output must not already exist."""
from pathlib import Path
import os,sys,resource,json,hashlib,re,zipfile,subprocess,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,resource.RLIM_INFINITY))
def lean_launcher_limits():
 resource.setrlimit(resource.RLIMIT_AS,(resource.RLIM_INFINITY,resource.RLIM_INFINITY))
 resource.setrlimit(resource.RLIMIT_CPU,(210,210))
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1')
L=Path(__file__).resolve().parent
out=Path(sys.argv[1]).resolve();out.mkdir()
pins=json.loads((L/'pins.json').read_text()); assert len(pins['packages'])==8
assert hashlib.sha256(Path(pins['lean_binary']).read_bytes()).hexdigest()==pins['lean_sha256']
def revision(repo):
 g=repo/'.git'
 if g.is_file():g=(repo/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 h=(g/'HEAD').read_text().strip()
 if not h.startswith('ref: '):return h
 r=h[5:]
 if (g/r).exists():return (g/r).read_text().strip()
 for s in (g/'packed-refs').read_text().splitlines():
  if s.endswith(' '+r):return s.split()[0]
 raise AssertionError(repo)
for p in pins['packages'].values():assert revision(Path(p['path']))==p['revision']
manifest=json.loads((L/'source-manifest.json').read_text());assert len(manifest)==2023
mods=json.loads((L/'consumed-modules.json').read_text());assert len(mods)==2022
assert (L/'fresh-plan.txt').read_text().splitlines()==mods+['FinalAudit']
# Make and extract an immutable, deterministic source-only replay input.
zpath=out/'replay-sources.zip'
with zipfile.ZipFile(zpath,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for f in sorted(list(manifest)+['pins.json','run.py']):
  data=(L/f).read_bytes()
  if f in manifest:assert hashlib.sha256(data).hexdigest()==manifest[f]['sha256']
  zi=zipfile.ZipInfo(f,(2026,10,29,0,0,0));zi.compress_type=zipfile.ZIP_DEFLATED;zi.external_attr=0o644<<16;z.writestr(zi,data)
E=out/'extracted';E.mkdir()
with zipfile.ZipFile(zpath) as z:z.extractall(E)
assert not list(E.rglob('*.olean')) and not list(E.rglob('*.ilean'))
(E/'logs').mkdir();F=E/'formal'
# Version probe uses the same bounded launcher as all Lean stages.
with (E/'logs/version.log').open('w') as log:
 subprocess.run([sys.executable,str(E/'run.py'),'--version'],preexec_fn=lean_launcher_limits,cwd=F,stdout=log,stderr=subprocess.STDOUT,check=True)
assert (E/'logs/version.log').read_text().strip()==pins['lean_version']
for idx,m in enumerate(mods+['FinalAudit']):
 with (E/'logs'/(m+'.log')).open('w') as log:
  subprocess.run([sys.executable,str(E/'run.py'),'-o',m+'.olean',m+'.lean'],preexec_fn=lean_launcher_limits,cwd=F,stdout=log,stderr=subprocess.STDOUT,check=True)
 with (out/'completed.txt').open('a') as f:f.write(m+'\n')
 if idx%50==0:print(idx+1,m,flush=True)
for m in mods:assert not (E/'logs'/(m+'.log')).read_text(),m
text=(E/'logs/FinalAudit.log').read_text();names=(F/'declaration-names.txt').read_text().splitlines()
blocks=re.findall(r'AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS ([^\n]+)',text,re.S)
assert len(blocks)==len(names)==len(set(names))==5924
assert set(n for _,n,_,_,_ in blocks)==set(names)
expected=json.loads((L/'inherited/declaration-inventory.json').read_text())
assert {v['name'] for v in expected}==set(names)
for origin,n,t,a,f in blocks:
 assert origin in mods
 assert f==('unsafe=false partial=true axiom=false' if n=='Polyomino57.attachCheck._unsafe_rec' else 'unsafe=false partial=false axiom=false'),(n,f)
 assert set(re.findall(r'[A-Za-z][A-Za-z.]*',a))<=set(['propext','Classical.choice','Quot.sound'])
inv=[dict(origin=m,name=n,type=t,axioms=a,flags=f) for m,n,t,a,f in blocks]
(out/'declaration-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
runs=[json.loads(s) for s in (E/'runs.jsonl').read_text().splitlines()];assert len(runs)==2024
assert all(r['rc']==0 and r['kill_reason'] is None and r['peak_group_rss']<2800*1024**2 and r['seconds']<230 and r['interval_seconds']==.045 for r in runs)
for f,v in manifest.items():assert hashlib.sha256((E/f).read_bytes()).hexdigest()==v['sha256']
receipt=dict(status='PASS',modules=2022,declarations=5924,stages=2023,version_probe=1,credit=0,root_acceptance=False,fresh_extraction=True,candidate_prebuilts=False,source_archive_sha256=hashlib.sha256(zpath.read_bytes()).hexdigest(),source_manifest_sha256=hashlib.sha256((L/'source-manifest.json').read_bytes()).hexdigest(),pins=pins,build_reports=runs,resource_qualification='45ms sampled group RSS; unsampled transients not excluded',endpoints=[v for v in inv if v['name'].startswith('Polyomino57.Diagonal.FiniteProof.AllCases.')])
(out/'REPLAY-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print('PASS',flush=True)
