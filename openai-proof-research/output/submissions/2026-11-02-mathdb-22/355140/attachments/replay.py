from pathlib import Path
import os,subprocess,resource,time,json,hashlib,zipfile,stat,sys
R=Path(__file__).resolve().parent
B=Path(os.environ.get('LEAN_BIN','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin'))
P=Path(os.environ.get('LEAN_PACKAGES','/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'))
W=R/'fresh';W.mkdir(exist_ok=False)
for name in ['Game.lean','Bridge.lean','Audit.lean']:
 (W/name).write_bytes((R/name).read_bytes())
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

for module in ['Game','Bridge']:
 assert run('strict-'+module,[str(B/'lean'),'-j1','-DwarningAsError=true','-o',module+'.olean',module+'.lean'])==0
assert run('all-declarations',[str(B/'lean'),'-j1','-DwarningAsError=true','Audit.lean'])==0
for module in ['Game','Bridge']:
 assert run('leanchecker-'+module,[str(B/'leanchecker'),module])==0
(W/'BadBound.lean').write_text('import Bridge\nexample : MathDB355140.check MathDB355140.graph ∅ Finset.univ true 3 = true := by rw [MathDB355140.three_check]; decide\n')
assert run('negative-three',[str(B/'lean'),'-j1','-DwarningAsError=true','BadBound.lean'])!=0
assert run('negative-missing',[str(B/'leanchecker'),'DefinitelyMissing355140'])!=0
(W/'Corrupt.olean').write_bytes((W/'Game.olean').read_bytes()[:64])
assert run('negative-corrupt',[str(B/'leanchecker'),'Corrupt'])!=0
print('ALL_REPLAY_CHECKS_PASSED')
