"""Read original packet, safely extract, fresh strict rebuild, audit entire local environment."""
from pathlib import Path,PurePosixPath
import os,sys,json,zipfile,hashlib,subprocess,time,resource,re
r=Path(__file__).resolve().parent
if (r/'SHA256SUMS.json').exists():
 for f,h in json.loads((r/'SHA256SUMS.json').read_text()).items():
  assert hashlib.sha256((r/f).read_bytes()).hexdigest()==h, f
out=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else r/'replay-output'
out.mkdir(parents=True,exist_ok=True); e=out/'extracted';e.mkdir(exist_ok=False)
packet=r/'candidate/proof-packet.zip'
with zipfile.ZipFile(packet) as z:
 for i in z.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not (i.external_attr>>16)&0o170000==0o120000
  assert i.file_size<40_000_000 and p.suffix not in ['.olean','.ilean','.so']
 z.extractall(e)
# Original packet is flat; assert rather than search untrusted directories.
assert (e/'WeakMarkov333569.lean').exists()
mods=['Target333569','Algebra333569','Curvature333569','Cylinders333569','Diagonal333569','SeriesCurvature333569','Entropy333569','Consistency333569','TwoSided333569','Stationarity333569','FiniteEntropy333569','Selected333569','SelectedEntropy333569','FairSelections333569','FairEntropy333569','EntropyLimit333569','TransverseEntropy333569','SeriesDerivatives333569','ParameterMaximum333569','SourceParameter333569','WeakMarkov333569']
for m in mods+['Audit333569']:
 assert (e/(m+'.lean')).read_bytes()==(r/'candidate'/(m+'.lean')).read_bytes()
(e/'IndependentInventory.lean').write_bytes((r/'IndependentInventory.lean').read_bytes())
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
assert hashlib.sha256(lean.read_bytes()).hexdigest()==json.loads((r/'candidate/pins.json').read_text())['lean_binary_sha256']
cache=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
packages=['mathlib','plausible','LeanSearchClient','importGraph','proofwidgets','aesop','Qq','batteries']
env={'PATH':'/usr/bin:/bin','HOME':str(out),'LANG':'C.UTF-8','LEAN_PATH':':'.join([str(e)]+[str(cache/p/'.lake/build/lib/lean') for p in packages])}
def limits():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(180,180));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
rows=[]
for m in mods+['Audit333569','IndependentInventory']:
 t=time.monotonic();q=subprocess.run([str(lean),'-j2','-M4096','-DwarningAsError=true','-o',m+'.olean',m+'.lean'],cwd=e,env=env,preexec_fn=limits,capture_output=True,text=True,timeout=240)
 (out/(m+'.log')).write_text(q.stdout+q.stderr);rows.append(dict(module=m,exit=q.returncode,wall_seconds=time.monotonic()-t));print(m,q.returncode,flush=True)
 (out/'progress.json').write_text(json.dumps(rows,indent=2))
 if q.returncode: raise SystemExit(1)
raw=(out/'IndependentInventory.log').read_text(); inv=[];allowed={'propext','Classical.choice','Quot.sound'}
for m,n,k,u,a in re.findall(r'INVENTORY\|([^|\n]+)\|([^|\n]+)\|([^|\n]+)\|([^|\n]+)\|\[([^\]]*)\]',raw):
 ax=re.findall(r'[\w.]+',a);inv.append(dict(module=m,name=n,kind=k,unsafe=u.strip()=='true',axioms=ax))
expected=json.loads((r/'fidelity-review/complete-inventory.json').read_text())
# Compare actual inventory names below in addition to the independent count.
named=json.loads((r/'candidate/audit-inventory.json').read_text()) if (r/'candidate/audit-inventory.json').exists() else re.findall(r"#print axioms (\S+)",(r/'candidate/Audit333569.lean').read_text())
assert {x['module'] for x in inv}==set(mods)
assert len(inv)==444 and len({x['name'] for x in inv})==444
oldlog=(r/'fidelity-review/complete-inventory.log').read_text()
assert {x['name'] for x in inv}==set(re.findall(r'INVENTORY\|[^|\n]+\|([^|\n]+)\|',oldlog))
assert set(named)<={x['name'] for x in inv}
assert not [x for x in inv if x['kind']=='axiom' or x['unsafe'] or set(x['axioms'])-allowed]
(out/'complete-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
res=dict(passed=True,modules=rows,all_local_declarations=len(inv),named=len(named),generated_additional=len(inv)-len(named),allowed_axioms=sorted(allowed),local_axioms=0,unsafe=0,violations=0,lean_sha256=hashlib.sha256(lean.read_bytes()).hexdigest(),packet_sha256=hashlib.sha256(packet.read_bytes()).hexdigest(),max_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,threads=2,affinity_max=2,memory_mb=4096,cpu_seconds_per_module=180,wall_seconds_per_module=240,external_prebuilt_oleans_and_exported_axiom_summaries_trusted=True,upstream_rebuilt=False)
(out/'replay.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
