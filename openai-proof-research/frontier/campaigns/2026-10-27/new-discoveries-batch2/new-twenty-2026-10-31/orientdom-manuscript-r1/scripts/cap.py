import os,sys,subprocess,time,resource,json,pathlib,signal
ROOT=pathlib.Path(__file__).resolve().parents[1]
name=sys.argv[1]; cmd=sys.argv[2:]; cpus=sorted(os.sched_getaffinity(0))[:2]
os.sched_setaffinity(0,cpus)
env=os.environ.copy(); env.update(MALLOC_ARENA_MAX='2',TMPDIR=str(ROOT/'tmp'),PYTHONDONTWRITEBYTECODE='1',XDG_CACHE_HOME=str(ROOT/'tmp'))
def limit():
 os.setsid(); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
t=time.monotonic(); p=subprocess.Popen(cmd,cwd=ROOT,env=env,preexec_fn=limit); peak=0; reason=None
while p.poll() is None:
 rss=0
 for d in pathlib.Path('/proc').iterdir():
  if d.name.isdigit():
   try:
    if os.getpgid(int(d.name))==p.pid:
     for line in (d/'status').read_text().splitlines():
      if line.startswith('VmRSS:'): rss+=int(line.split()[1])*1024
   except (OSError,ProcessLookupError): pass
 peak=max(peak,rss)
 if rss>6*1024**3 or time.monotonic()-t>140:
  reason='RSS' if rss>6*1024**3 else 'wall'; os.killpg(p.pid,signal.SIGKILL); break
 time.sleep(.05)
rc=p.wait(); (ROOT/'receipts'/f'{name}.json').write_text(json.dumps(dict(command=cmd,cpus=cpus,exit=rc,wall_seconds=time.monotonic()-t,sampled_peak_rss=peak,reason=reason,cpu_limit=120,wall_limit=140,rss_limit=6*1024**3),indent=2)+'\n'); sys.exit(rc)
