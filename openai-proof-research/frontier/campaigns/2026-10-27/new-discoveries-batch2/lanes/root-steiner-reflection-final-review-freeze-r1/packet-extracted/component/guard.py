import os,sys,resource,subprocess,time,signal,json,hashlib
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,resource.RLIM_INFINITY))
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,)*2)
signal.alarm(240)
ROOT=Path(__file__).resolve().parent
BASE=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
LEAN='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
assert hashlib.sha256(Path(LEAN).read_bytes()).hexdigest()=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
env=os.environ.copy();env.update({k:'1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','BLIS_NUM_THREADS','NUMEXPR_NUM_THREADS']})
env['LEAN_PATH']=':'.join([str(ROOT/'formal')]+[str(p) for p in (BASE/'.lake/packages').glob('*/.lake/build/lib/lean')])
def child():
 resource.setrlimit(resource.RLIMIT_AS,(resource.RLIM_INFINITY,)*2)
 resource.setrlimit(resource.RLIMIT_CPU,(210,210))
name=sys.argv[1]; cmd=[LEAN,'-j1','-M2700','-DwarningAsError=true','-DautoImplicit=false','-o',name+'.olean',name+'.lean']
t=time.monotonic();peak=0;reason=None
with (ROOT/'logs'/f'{name}.log').open('w') as out:
 p=subprocess.Popen(cmd,cwd=ROOT/'formal',env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=child)
 resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,resource.RLIM_INFINITY))
 while p.poll() is None:
  sample_start=time.monotonic();rss=0;cpu_ticks=0
  for f in Path('/proc').glob('[0-9]*/stat'):
   try:
    fields=f.read_text().rsplit(')',1)[1].split()
    if int(fields[2])==p.pid:
     rss+=int(fields[21])*os.sysconf('SC_PAGE_SIZE')//1024
     cpu_ticks+=int(fields[11])+int(fields[12])
   except (FileNotFoundError,ProcessLookupError,PermissionError):pass
  peak=max(peak,rss)
  if rss>2800*1024:reason='RSS'
  if cpu_ticks/os.sysconf('SC_CLK_TCK')>210:reason='CPU'
  if time.monotonic()-t>230:reason='wall'
  if reason:os.killpg(p.pid,signal.SIGKILL)
  time.sleep(max(0,.045-(time.monotonic()-sample_start)))
 code=p.wait()
r={'command':cmd,'exit':code,'peak_group_rss_kib':peak,'sample_seconds':.045,'cpu_limit':210,'wall_limit':230,'kill':reason,'seconds':time.monotonic()-t}
(ROOT/'logs'/f'{name}.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r));
if code:print((ROOT/'logs'/f'{name}.log').read_text())
sys.exit(code)
