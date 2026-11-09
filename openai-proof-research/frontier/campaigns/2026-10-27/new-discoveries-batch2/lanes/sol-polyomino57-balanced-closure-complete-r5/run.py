import os,sys,time,json,signal,subprocess,hashlib,resource
from pathlib import Path
L=Path(__file__).resolve().parent
p=json.loads((L/'pins.json').read_text()); assert hashlib.sha256(Path(p['lean_binary']).read_bytes()).hexdigest()==p['lean_sha256']
e=dict(os.environ); e['LEAN_PATH']=str(Path.cwd())+':'+':'.join(v['path']+'/.lake/build/lib/lean' for v in p['packages'].values())
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'): e[k]='1'
t=time.monotonic(); peak=0; why=None
q=subprocess.Popen([p['lean_binary'],'-j1','-DwarningAsError=true','-DautoImplicit=false',*sys.argv[1:]],env=e,start_new_session=True,preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_CPU,(210,215)))
# Only Lean has the separate monitored memory allowance. The supervisor itself
# receives its hard 512 MiB AS bound after spawning that process.
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(30,35))
while q.poll() is None:
 rss=0
 for d in Path('/proc').iterdir():
  if d.name.isdigit():
   try:
    if os.getpgid(int(d.name))==q.pid:
     rss+=int((d/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
   except (OSError,ProcessLookupError,ValueError): pass
 peak=max(peak,rss)
 if rss>=2800*1024**2 or time.monotonic()-t>220:
  why='rss' if rss>=2800*1024**2 else 'wall'; os.killpg(q.pid,signal.SIGKILL); break
 time.sleep(.045)
rc=q.wait(); report=dict(args=sys.argv[1:],rc=rc,seconds=time.monotonic()-t,peak_group_rss=peak,interval_seconds=.045,kill_reason=why)
with (L/'runs.jsonl').open('a') as f: f.write(json.dumps(report)+'\n')
sys.exit(rc)
