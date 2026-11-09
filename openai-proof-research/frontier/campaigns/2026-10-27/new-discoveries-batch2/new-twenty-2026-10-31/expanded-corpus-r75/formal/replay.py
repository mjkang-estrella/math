#!/usr/bin/env python3
"""Fresh local replay with explicit read-only prebuilt dependencies; no network or git commands."""
import argparse,pathlib,json,hashlib,os,subprocess,resource,time,signal,re,shutil
p=argparse.ArgumentParser();p.add_argument('--source',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);p.add_argument('--packages',type=pathlib.Path,required=True);p.add_argument('--lean-bin',type=pathlib.Path,required=True);a=p.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
assert not list(out.glob('*.olean')),'output must be fresh'
for f in ['Magic.lean','Audit.lean']:shutil.copyfile(a.source/f,out/f)
paths=[str(x/'.lake/build/lib/lean') for x in a.packages.resolve().iterdir() if (x/'.lake/build/lib/lean').is_dir()]
env={**os.environ,'LEAN_PATH':':'.join(paths+[str(out)]),'PATH':str(a.lean_bin.resolve())+':'+os.environ['PATH'],'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'2'}
def pre():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
def run(name,args):
 t=time.monotonic();peak=0;reason=None
 with (out/(name+'.log')).open('w') as f:
  pr=subprocess.Popen(args,cwd=out,env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=pre)
  while pr.poll() is None:
   try:rss=int(next(s.split()[1] for s in pathlib.Path(f'/proc/{pr.pid}/status').read_text().splitlines() if s.startswith('VmRSS:')))*1024;peak=max(peak,rss)
   except (OSError,StopIteration):pass
   if peak>6*1024**3 or time.monotonic()-t>140:reason='cap';os.killpg(pr.pid,signal.SIGKILL);break
   time.sleep(.05)
  pr.wait()
 receipt=dict(returncode=pr.returncode,wall_seconds=time.monotonic()-t,sampled_RSS_bytes=peak,cap_reason=reason)
 (out/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2));assert pr.returncode==0,(name,receipt)
 return receipt
v=subprocess.check_output([str(a.lean_bin/'lean'),'--version'],env=env,text=True);assert '4.34.1' in v
r={};r['build']=run('build',['lean','-j1','-DwarningAsError=true','-o','Magic.olean','Magic.lean']);r['audit']=run('audit',['lean','-j1','-DwarningAsError=true','Audit.lean']);log=(out/'audit.log').read_text();assert 'COUNT|37' in log and len(re.findall(r'^DECL\|',log,re.M))==37
r['leanchecker']=run('leanchecker',['leanchecker','Magic']);r['source_sha256']={f:hashlib.sha256((out/f).read_bytes()).hexdigest() for f in ['Magic.lean','Audit.lean']};r['trust_limits']=['External prebuilt pinned dependency oleans; no full upstream rebuild','leanchecker shares Lean kernel','50ms RSS sampling is not a cgroup/transient-peak guarantee'];(out/'replay-result.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
