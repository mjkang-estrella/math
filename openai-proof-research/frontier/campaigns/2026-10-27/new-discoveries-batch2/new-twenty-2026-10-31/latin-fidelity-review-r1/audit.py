from pathlib import Path
import os, json, hashlib, zipfile, stat, subprocess, resource, time
L=Path(__file__).resolve().parent; B=L.parent; A=B/'expanded-corpus-r40'
F=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal'); T=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
E=L/'fresh';E.mkdir(exist_ok=True)
with zipfile.ZipFile(A/'lean-packet.zip') as z:
 entries=[]
 for i in z.infolist():
  p=Path(i.filename);assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
  assert i.filename=='Latin.lean'; entries.append({'name':i.filename,'size':i.file_size,'mode':i.external_attr>>16});(E/p).write_bytes(z.read(i))
assert H(E/'Latin.lean')=='7c93a368b2d7007aa10102cb7bb92ca5f3585cc4bd46a2d54c26c859d46c5392'
assert H(A/'lean-packet.zip')=='9436c0bb8fd37c9dc16ad09bfcb20fd85cabd3eb192a74babe870d357b59c9b4'
assert not list(E.glob('*.olean'))
(L/'packet-inspection.json').write_text(json.dumps(entries,indent=2))
paths=[str(E)]+[str(p/'.lake/build/lib/lean') for p in sorted((F/'.lake/packages').iterdir())]
env={'PATH':str(T)+':/usr/bin:/bin','HOME':str(L),'LANG':'C.UTF-8','LEAN_PATH':':'.join(paths)}
cpus=sorted(os.sched_getaffinity(0))[:2]
def limits():
 os.sched_setaffinity(0,cpus);resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
receipts=[]
def run(label,cmd,wall=110):
 start=time.monotonic()
 try:
  r=subprocess.run(cmd,cwd=E,env=env,preexec_fn=limits,capture_output=True,timeout=wall);code=r.returncode;out=r.stdout;err=r.stderr
 except subprocess.TimeoutExpired as r:code='timeout';out=r.stdout or b'';err=r.stderr or b''
 (L/(label+'.stdout')).write_bytes(out);(L/(label+'.stderr')).write_bytes(err)
 receipt={'label':label,'command':cmd,'exit_code':code,'wall_seconds':time.monotonic()-start,'CPU_seconds_limit':100,'AS_bytes':8*1024**3,'cpus':cpus,'wall_limit':wall};receipts.append(receipt);(L/'run-receipts.json').write_text(json.dumps(receipts,indent=2));print(receipt,flush=True);return code
assert run('author-strict',[str(T/'lean'),'-j1','-DwarningAsError=true','-o','Latin.olean','Latin.lean'])==0
# Independent audit of all constants originating in Latin, including private/generated names.
audit='''import Latin
open Lean in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (n, ci) in env.constants.toList do
  let origin := (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!
  if origin == some `Latin then
   count := count + 1
   let axs ← Lean.collectAxioms n
   logInfo m!"INDEPENDENT {n} ORIGIN {origin} TYPE {ci.type} AXIOMS {axs}"
   if ci.isUnsafe then throwError "unsafe {n}"
   if ci matches .axiomInfo _ then throwError "axiom {n}"
   for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
     throwError "forbidden {ax}"
 logInfo m!"INDEPENDENT_TOTAL {count}"
 if count != 22 then throwError "unexpected count {count}"
'''
(E/'AuthorAudit.lean').write_text(audit)
assert run('author-independent-audit',[str(T/'lean'),'-j1','-DwarningAsError=true','AuthorAudit.lean'])==0
assert run('checker-author',[str(T/'leanchecker'),'Latin'])==0
(E/'Negative.lean').write_text('import Latin\ntheorem rejected : False := by\n  exact True.intro\n')
assert run('negative-lean',[str(T/'lean'),'-j1','-DwarningAsError=true','-o','Negative.olean','Negative.lean'])!=0
# Corrupt module negative control tests checker rejection, not a forged theorem proof.
(E/'Corrupt.olean').write_bytes(b'not a Lean module\x00')
assert run('negative-checker',[str(T/'leanchecker'),'Corrupt'])!=0
(L/'dependency-provenance.json').write_text(json.dumps({'lean_version':subprocess.check_output([str(T/'lean'),'--version'],env=env,text=True).strip(),'lean_sha256':H(T/'lean'),'leanchecker_sha256':H(T/'leanchecker'),'manifest':json.loads((F/'lake-manifest.json').read_text()),'manifest_sha256':H(F/'lake-manifest.json'),'lean_path':paths,'environment':env,'trust':'Prebuilt imported dependency oleans trusted, no complete upstream rebuild.'},indent=2))
