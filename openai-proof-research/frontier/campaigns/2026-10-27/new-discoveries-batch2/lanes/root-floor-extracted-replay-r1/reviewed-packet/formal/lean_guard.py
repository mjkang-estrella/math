"""Dedicated serial Lean guard: fixed 2800MiB group RSS, CPU210, wall230."""
import os,sys,time,resource,subprocess,signal,json
from pathlib import Path
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
LEAN='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(Path.cwd())]+[str(p/'.lake/build/lib/lean') for p in sorted(P.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]))
env.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
def pre():resource.setrlimit(resource.RLIMIT_CPU,(210,210))
log=Path(sys.argv[1]);cmd=[LEAN,'-j1','-M2700','-DwarningAsError=true','-DautoImplicit=false',*sys.argv[2:]]
start=time.monotonic();peak=0;reason=None;hz=os.sysconf('SC_CLK_TCK')
with log.open('w') as out:
 p=subprocess.Popen(['prlimit','--as=unlimited','--',*cmd],stdout=out,stderr=subprocess.STDOUT,env=env,start_new_session=True,preexec_fn=pre)
 while p.poll() is None:
  rss=cpu=0
  for name in os.listdir('/proc'):
   if not name.isdigit():continue
   try:
    data=Path('/proc/'+name+'/stat').read_text().rsplit(')',1)[1].split()
    if int(data[2])!=p.pid:continue
    rss+=int(data[21])*os.sysconf('SC_PAGE_SIZE');cpu+=(int(data[11])+int(data[12]))/hz
   except (FileNotFoundError,ProcessLookupError,PermissionError):pass
  peak=max(peak,rss)
  if rss>2800*1024**2:reason='group RSS2800MiB'
  if cpu>210:reason='group CPU210'
  if time.monotonic()-start>230:reason='wall230'
  if reason:os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.04)
 code=p.wait()
r={'command':cmd,'exit_code':code,'reason':reason,'sampled_peak_group_rss':peak,'wall_seconds':time.monotonic()-start,'sample_interval':.04,'AS':'no separate AS cap; Lean -M2700; RSS2800MiB'}
log.with_suffix('.guard.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
with log.open() as f:print(f.read(10000))
sys.exit(code if code>=0 else 128-code)
