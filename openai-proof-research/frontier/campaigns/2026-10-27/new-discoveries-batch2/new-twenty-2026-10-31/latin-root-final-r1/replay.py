"""Fresh source-only extraction and strict replay; writes only beside this script.
Adapted from the frozen fidelity review runners. Never invokes author replay.py.
"""
from pathlib import Path, PurePosixPath
import os,json,hashlib,zipfile,stat,subprocess,resource,time,re,tempfile
L=Path(__file__).resolve().parent
T=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
F=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected={'Latin.lean':'7c93a368b2d7007aa10102cb7bb92ca5f3585cc4bd46a2d54c26c859d46c5392','Supplement.lean':'47624020f01dda04bed4017512b5b0c1f9ddf31039d36f8bb52f20fd40bdc353'}
E=Path(tempfile.mkdtemp(prefix='replay-',dir=L));logs=E/'logs';logs.mkdir()
with zipfile.ZipFile(L/'proof-source.zip') as z:
 assert len(z.infolist())==2 and set(z.namelist())==set(expected)
 entries=[]
 for i in z.infolist():
  p=PurePosixPath(i.filename);mode=i.external_attr>>16
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename
  assert not stat.S_ISLNK(mode) and i.filename in expected
  (E/i.filename).write_bytes(z.read(i));assert H(E/i.filename)==expected[i.filename]
  entries.append({'name':i.filename,'mode':mode,'size':i.file_size,'sha256':H(E/i.filename)})
assert not list(E.glob('*.olean'))
paths=[str(E)]+[str(p/'.lake/build/lib/lean') for p in sorted((F/'.lake/packages').iterdir())]
env={'PATH':str(T)+':/usr/bin:/bin','HOME':str(E),'LANG':'C.UTF-8','LEAN_PATH':':'.join(paths)}
cpus=sorted(os.sched_getaffinity(0))[:2]
def limits():
 os.sched_setaffinity(0,cpus);resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
receipts=[]
def run(label,cmd,success=True):
 start=time.monotonic()
 try:
  r=subprocess.run(cmd,cwd=E,env=env,preexec_fn=limits,capture_output=True,timeout=110);code=r.returncode;out=r.stdout;err=r.stderr
 except subprocess.TimeoutExpired as r:code='timeout';out=r.stdout or b'';err=r.stderr or b''
 (logs/(label+'.stdout')).write_bytes(out);(logs/(label+'.stderr')).write_bytes(err)
 receipts.append({'label':label,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'AS_bytes':8*1024**3,'CPU_seconds':100,'wall_seconds':110,'cpus':cpus})
 (E/'run-receipts.json').write_text(json.dumps(receipts,indent=2));print(receipts[-1],flush=True)
 assert (code==0) if success else (isinstance(code,int) and code!=0)
for name in expected:
 # Proof-level forbidden tokens; audit rejection strings and comments are excluded.
 s=(E/name).read_text().split('open Lean in')[0];s=re.sub(r'--[^\n]*','',s)
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',s)
for module,count in [('Latin',22),('Supplement',17)]:
 run(module+'-strict',[str(T/'lean'),'-j1','-DwarningAsError=true','-o',module+'.olean',module+'.lean'])
 audit=f'''import {module}
set_option pp.all true
open Lean in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (n, ci) in env.constants.toList do
  let origin := (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!
  if origin == some `{module} then
   count := count + 1
   let axs ← Lean.collectAxioms n
   logInfo m!"DECL {{n}} ORIGIN {{origin}} TYPE {{ci.type}} AXIOMS {{axs}}"
   if ci.isUnsafe then throwError "unsafe {{n}}"
   if ci matches .axiomInfo _ then throwError "custom axiom {{n}}"
   for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
     throwError "forbidden {{ax}}"
 logInfo m!"AUDIT_TOTAL {{count}}"
 if count != {count} then throwError "unexpected count {{count}}"
'''
 (E/(module+'Audit.lean')).write_text(audit)
 run(module+'-audit',[str(T/'lean'),'-j1','-DwarningAsError=true',module+'Audit.lean'])
 run(module+'-checker',[str(T/'leanchecker'),module])
(E/'Negative.lean').write_text('import Latin\ntheorem rejected : False := by\n exact True.intro\n')
run('negative-lean',[str(T/'lean'),'-j1','-DwarningAsError=true','Negative.lean'],False)
(E/'Corrupt.olean').write_bytes(b'not a Lean module\x00')
run('negative-checker',[str(T/'leanchecker'),'Corrupt'],False)
prov={'environment':env,'lean_version':subprocess.check_output([str(T/'lean'),'--version'],env=env,text=True).strip(),'lean_sha256':H(T/'lean'),'leanchecker_sha256':H(T/'leanchecker'),'manifest':json.loads((F/'lake-manifest.json').read_text()),'manifest_sha256':H(F/'lake-manifest.json'),'mathlib_head':(F/'.lake/packages/mathlib/.git/HEAD').read_text().strip(),'trust_limit':'Imported package olean caches trusted; no complete upstream rebuild or source-to-olean attestation.'}
assert prov['mathlib_head']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
(E/'dependency-provenance.json').write_text(json.dumps(prov,indent=2))
result={'status':'PASS','directory':str(E),'packet_sha256':H(L/'proof-source.zip'),'entries':entries,'declarations':{'Latin':22,'Supplement':17},'allowlist':['propext','Classical.choice','Quot.sound'],'runs':receipts,'trust_limit':prov['trust_limit']}
(E/'receipt.json').write_text(json.dumps(result,indent=2));(L/'replay-result.json').write_text(json.dumps(result,indent=2))
