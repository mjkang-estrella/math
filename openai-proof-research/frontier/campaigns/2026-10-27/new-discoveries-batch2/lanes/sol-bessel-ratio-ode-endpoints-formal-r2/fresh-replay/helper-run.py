import os,sys,time,json,signal,subprocess,resource
from pathlib import Path
L=Path(__file__).resolve().parent
CAP=512*1024**2
resource.setrlimit(resource.RLIMIT_AS,(CAP,CAP))
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
e=dict(os.environ)
e.update({k:'1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']})
t=time.monotonic(); peak=0; why=None
q=subprocess.Popen([sys.executable,*sys.argv[1:]],env=e,start_new_session=True)
while q.poll() is None:
 rss=0; cpu=0
 for d in Path('/proc').iterdir():
  if d.name.isdigit():
   try:
    if os.getpgid(int(d.name))==q.pid:
     rss+=int((d/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
     st=(d/'stat').read_text().rsplit(')',1)[1].split(); cpu+=(int(st[11])+int(st[12]))/os.sysconf('SC_CLK_TCK')
   except (OSError,ProcessLookupError,ValueError): pass
 peak=max(peak,rss)
 if rss>=CAP or time.monotonic()-t>230 or cpu>210:
  why='rss' if rss>=CAP else 'wall' if time.monotonic()-t>230 else 'cpu'
  os.killpg(q.pid,signal.SIGKILL); break
 time.sleep(.045)
rc=q.wait()
with (L/'helper-runs.jsonl').open('a') as f:
 f.write(json.dumps(dict(args=sys.argv[1:],rc=rc,seconds=time.monotonic()-t,peak_group_rss=peak,interval_seconds=.045,kill_reason=why))+'\n')
sys.exit(rc)
