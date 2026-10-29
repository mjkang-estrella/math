import os,sys,time,json,signal,subprocess,hashlib,resource
from pathlib import Path
L=Path(__file__).resolve().parent
p=json.loads((L/'pins.json').read_text()); assert hashlib.sha256(Path(p['lean_binary']).read_bytes()).hexdigest()==p['lean_sha256']
e=dict(os.environ); e['LEAN_PATH']=str(Path.cwd())+':'+':'.join(v['path']+'/.lake/build/lib/lean' for v in p['packages'].values())
e.update({k:'1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']})
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(210,210))
t=time.monotonic(); peak=0; why=None
q=subprocess.Popen([p['lean_binary'],'-j1','-DwarningAsError=true','-DautoImplicit=false',*sys.argv[1:]],env=e,start_new_session=True,preexec_fn=limits)
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
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
 if rss>=2800*1024**2 or time.monotonic()-t>230 or cpu>210:
  why='rss' if rss>=2800*1024**2 else 'wall'; os.killpg(q.pid,signal.SIGKILL); break
 time.sleep(.045)
rc=q.wait(); report=dict(args=sys.argv[1:],rc=rc,seconds=time.monotonic()-t,peak_group_rss=peak,interval_seconds=.045,kill_reason=why)
with (L/'runs.jsonl').open('a') as f: f.write(json.dumps(report)+'\n')
sys.exit(rc)
