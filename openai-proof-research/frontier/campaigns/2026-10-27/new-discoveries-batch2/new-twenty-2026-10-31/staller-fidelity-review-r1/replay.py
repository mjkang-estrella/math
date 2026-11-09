from pathlib import Path
import os,subprocess,resource,time,json,hashlib,zipfile,stat
R=Path(__file__).resolve().parent; A=R.parent/'expanded-corpus-r48'; B=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin'); P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
W=R/'extracted';W.mkdir(exist_ok=False)
z=zipfile.ZipFile(A/'355140-proof-source.zip'); members=[]
for i in z.infolist():
 p=Path(i.filename)
 assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
 assert p.suffix not in ['.olean','.ilean','.so']
 members.append({'name':i.filename,'bytes':i.file_size})
z.extractall(W); (R/'zip-members.json').write_text(json.dumps(members,indent=2))
assert (W/'Game.lean').read_bytes()==(A/'Game.lean').read_bytes()
cpus=sorted(os.sched_getaffinity(0))[:2]
env={'PATH':str(B)+':/usr/bin:/bin','HOME':str(R),'LANG':'C.UTF-8','MALLOC_ARENA_MAX':'2','LEAN_PATH':':'.join([str(W)]+[str(q/'.lake/build/lib/lean') for q in sorted(P.iterdir()) if q.is_dir()])}
(R/'sanitized-env.json').write_text(json.dumps(env,indent=2))
def limit():
 os.sched_setaffinity(0,cpus);resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,)*2);resource.setrlimit(resource.RLIMIT_CPU,(120,)*2)
def run(name,args):
 s=time.monotonic(); peak=0; reason=None
 with (R/(name+'.log')).open('w') as out:
  p=subprocess.Popen(args,cwd=W,env=env,preexec_fn=limit,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
  while p.poll() is None:
   try:
    for l in Path(f'/proc/{p.pid}/status').read_text().splitlines():
     if l.startswith('VmRSS:'):peak=max(peak,int(l.split()[1])*1024)
   except FileNotFoundError: pass
   if peak>6*1024**3 or time.monotonic()-s>140:
    import signal
    reason='RSS/wall cap';os.killpg(p.pid,signal.SIGKILL)
   time.sleep(.025)
  rc=p.wait()
 d={'command':args,'exit':rc,'wall_s':time.monotonic()-s,'peak_sampled_RSS_bytes':peak,'reason':reason,'cpus':cpus,'RSS_cap':6*1024**3,'AS_cap':12*1024**3,'CPU_s':120,'wall_s_cap':140}
 (R/(name+'.json')).write_text(json.dumps(d,indent=2)); print(name,d,flush=True);return rc
assert run('strict-rebuild',[str(B/'lean'),'-j1','-DwarningAsError=true','-o','Game.olean','Game.lean'])==0
# Enumerate from the freshly compiled module, including generated names. Print full types and proof terms.
(W/'Inventory.lean').write_text('''import Game
set_option pp.all true
set_option pp.proofs true
open Lean in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (n, ci) in env.constants.toList do
  if (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?) == some `Game then
   count := count + 1
   logInfo m!"LOCAL {n} TYPE {ci.type}"
   if let some val := ci.value? then logInfo m!"VALUE {n} {val}"
   if ci.isUnsafe then throwError "unsafe {n}"
   if ci matches .axiomInfo _ then throwError "new axiom {n}"
   let axs ← Lean.collectAxioms n
   logInfo m!"TRANSITIVE_AXIOMS {n} {axs}"
   for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
     throwError "forbidden axiom {n} {ax}"
   elabCommand (← `(command| #print axioms $(mkIdent n)))
 logInfo m!"LOCAL_TOTAL {count}"
'''.replace('open Lean in','open Lean Elab Command in'))
run('inventory',[str(B/'lean'),'-j1','-DwarningAsError=true','Inventory.lean'])
run('leanchecker',[str(B/'leanchecker'),'Game'])
run('leanchecker-missing',[str(B/'leanchecker'),'DefinitelyMissing355140'])
