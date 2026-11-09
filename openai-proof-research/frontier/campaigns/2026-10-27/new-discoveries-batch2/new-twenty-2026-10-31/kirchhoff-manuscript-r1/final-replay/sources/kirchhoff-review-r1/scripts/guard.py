import os,resource,subprocess,sys,time,signal,json
from pathlib import Path
D=Path(__file__).resolve().parents[1]
name=sys.argv[1]; cmd=sys.argv[2:]
def limits():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120))
env=dict(os.environ,MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1',HOME=str(D),TMPDIR=str(D/'outputs'))
env['PATH']='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:'+env.get('PATH','')
env['LEAN_PATH']=':'.join([str(D/'fresh/formal')]+[str(p) for p in Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages').glob('*/.lake/build/lib/lean')])
t=time.monotonic();peak=0;reason=None
with (D/'logs'/f'{name}.log').open('w') as f:
 p=subprocess.Popen(cmd,cwd=D/'fresh/formal',env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits,start_new_session=True)
 try:
  while p.poll() is None:
   rss=0
   for x in Path('/proc').iterdir():
    if not x.name.isdecimal():continue
    try:
     if os.getpgid(int(x.name))==p.pid:
      rss+=sum(int(v.split()[1])*1024 for v in (x/'smaps_rollup').read_text().splitlines() if v.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')))
    except OSError:pass
   peak=max(peak,rss)
   if rss>6*1024**3:reason='RSS'
   if time.monotonic()-t>140:reason='wall'
   if reason:os.killpg(p.pid,signal.SIGKILL)
   time.sleep(.05)
 finally:
  if p.poll() is None:os.killpg(p.pid,signal.SIGKILL)
  rc=p.wait()
r=dict(command=cmd,returncode=rc,wall_seconds=time.monotonic()-t,peak_private_rss=peak,killed=reason)
(D/'receipts'/f'{name}.json').write_text(json.dumps(r,indent=2));print(json.dumps(r),flush=True)
sys.exit(rc)
