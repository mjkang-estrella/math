import resource,signal,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
import hashlib,json,shutil,zipfile,datetime
from pathlib import Path
R=Path(__file__).resolve().parent;B=R.parent
BASE=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
LEAN=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
def rev(p):
 g=p/'.git'
 if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 h=(g/'HEAD').read_text().strip()
 if h.startswith('ref: '):
  ref=h[5:];f=g/ref
  h=f.read_text().strip() if f.exists() else next(x.split()[0] for x in (g/'packed-refs').read_text().splitlines() if x.endswith(' '+ref))
 return h
pkgs=[]
for item in json.loads((BASE/'lake-manifest.json').read_text())['packages']:
 p=BASE/'.lake/packages'/item['name'];assert rev(p)==item['rev']
 pkgs.append({'name':item['name'],'path':str(p),'rev':item['rev']})
assert pkgs[0]['rev']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
(R/'pins.json').write_text(json.dumps({'lean_version':'4.34.1','lean_binary':str(LEAN/'bin/lean'),'lean_sha256':sha(LEAN/'bin/lean'),'packages':pkgs},indent=2)+'\n')
entries=[]
inputs=[B/'sol-fresh-source-discovery-r57/discovery.md',B/'sol-bessel-ratio-eligibility-review-r1/review.md',B/'root-bessel-ratio-adjudication-r1/ADJUDICATION.json',B.parent/'AGENTS.md',R.parents[5]/'AGENTS.md',BASE/'lake-manifest.json',BASE/'lean-toolchain',B/'sol-steiner-reflection-source-formal-r1/guard.py']
for i,p in enumerate(inputs):
 h=sha(p);dst=R/'frozen'/f'{i:02d}-{p.name}';shutil.copyfile(p,dst)
 assert h==sha(dst)==sha(p)
 entries.append({'origin':str(p),'sha256':h,'copy':str(dst.relative_to(R))})
(R/'provenance.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'inputs':entries,'external_access':False,'changing_series_worker_files_consumed':False,'guard_origin':'sol-steiner-reflection-source-formal-r1/guard.py','guard_adaptation':'Python alarm tightened from240 to230 seconds; limits otherwise unchanged','scope':'Generic conditional comparison component only; no literal Bessel endpoint','credit':0,'novelty':'HOLD'},indent=2)+'\n')
roots=[Path(p['path'])/'.lake/build/lib/lean' for p in pkgs]+[LEAN/'lib/lean']
deps=[]
for mod in (R/'formal/dependencies.txt').read_text().splitlines():
 if mod in ['Crossing','Transfer','Cases']:continue
 rel=Path(*mod.split('.'))
 hits=[root/rel.with_suffix('.olean') for root in roots if (root/rel.with_suffix('.olean')).exists()]
 assert len(hits)==1,(mod,hits)
 p=hits[0]
 for f in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if f.exists():deps.append({'path':str(f),'sha256':sha(f)})
 # Record corresponding source whenever available, independently of binary pin.
 for root in [Path(p['path']) for p in pkgs]+[LEAN/'src/lean']:
  f=root/rel.with_suffix('.lean')
  if f.exists():deps.append({'path':str(f),'sha256':sha(f)})
(R/'dependency-hashes.json').write_text(json.dumps(deps,indent=2)+'\n')
files=['guard.py','replay.py','pins.json','provenance.json','dependency-hashes.json']+[str(p.relative_to(R)) for p in sorted((R/'formal').glob('*.lean'))]+[str(p.relative_to(R)) for p in sorted((R/'frozen').iterdir())]
manifest={n:sha(R/n) for n in files};(R/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(R/'one-crossing-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for n in files+['manifest.json']:z.write(R/n,n)
print('PACKAGED',len(files),'files;',len(deps),'dependency hashes')
