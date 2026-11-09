# Capped Lean invocation: 2 CPUs, CPU 120 s, wall 140 s, sampled private RSS 6 GiB (process group), AS 64 GiB.
import os,sys,json,pathlib,subprocess,resource,signal,time
D=pathlib.Path(__file__).resolve().parents[1]
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
F=D/'lean/proof'
label=sys.argv[1]; cmd=sys.argv[2:]
env=dict(os.environ,PATH=str(B)+':/usr/bin:/bin',LEAN_PATH=':'.join([str(F)]+[str(x/'.lake/build/lib/lean') for x in sorted(P.iterdir()) if x.is_dir()]),LEAN_NUM_THREADS='1',MALLOC_ARENA_MAX='2')
cpus=sorted(os.sched_getaffinity(0))[:2]
def setup():
 os.setsid();os.sched_setaffinity(0,cpus);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
(D/'logs').mkdir(exist_ok=True)
start=time.monotonic();peak=0;reason=None
with (D/'logs'/(label+'.log')).open('w') as out:
 p=subprocess.Popen([str(B/cmd[0])]+cmd[1:],cwd=F,env=env,preexec_fn=setup,stdout=out,stderr=subprocess.STDOUT)
 while p.poll() is None:
  priv=0
  for q in pathlib.Path('/proc').glob('[0-9]*/status'):
   try:
    if os.getpgid(int(q.parent.name))!=p.pid:continue
    d={s.split(':')[0]:int(s.split()[1])*1024 for s in q.read_text().splitlines() if s.startswith(('RssAnon:','RssShmem:'))}
    priv+=d.get('RssAnon',0)+d.get('RssShmem',0)
   except (OSError,ValueError,ProcessLookupError):pass
  peak=max(peak,priv)
  if priv>6*1024**3 or time.monotonic()-start>140:
   reason='private-RSS' if priv>6*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 p.wait()
r=dict(label=label,command=cmd,exit=p.returncode,wall_seconds=time.monotonic()-start,peak_private_rss_bytes=peak,kill_reason=reason,cpus=cpus)
(D/'logs'/(label+'.json')).write_text(json.dumps(r,indent=2)+'\n');print(r)
print((D/'logs'/(label+'.log')).read_text()[-6000:])
