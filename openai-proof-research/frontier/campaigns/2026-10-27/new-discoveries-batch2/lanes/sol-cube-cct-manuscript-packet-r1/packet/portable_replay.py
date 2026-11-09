"""Dedicated fixed Lean runner; ordinary helper checks remain separately guarded."""
from pathlib import Path
import os,sys,subprocess,resource,time,signal,json
P=Path(__file__).resolve().parent;F=P/'formal'
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
def helper(*args):subprocess.run([sys.executable,str(P/'helper_guard.py'),sys.executable,str(P/'audit_packet.py'),*args],check=True)
helper('--pins-only')
lean=os.environ.get('CUBE_LEAN','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
pk=Path(os.environ.get('CUBE_PACKAGES','/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'))
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(F)]+[str(p/'.lake/build/lib/lean') for p in sorted(pk.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]))
def limits():resource.setrlimit(resource.RLIMIT_CPU,(210,210))
for mod in ['Finite','Cube','Endpoint','Audit']:
 cmd=[lean,'-j1','-M2700','-DwarningAsError=true','-DautoImplicit=false']+([] if mod=='Audit' else ['-o',mod+'.olean'])+[mod+'.lean']
 start=time.monotonic();peak=0;reason=None;hz=os.sysconf('SC_CLK_TCK')
 with (F/(mod+'.log')).open('w') as log:
  proc=subprocess.Popen(cmd,cwd=F,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
  while proc.poll() is None:
   rss=cpu=0
   for n in os.listdir('/proc'):
    if not n.isdigit():continue
    try:
     d=Path('/proc',n,'stat').read_text().rsplit(')',1)[1].split()
     if int(d[2])!=proc.pid:continue
     rss+=int(d[21])*os.sysconf('SC_PAGE_SIZE');cpu+=(int(d[11])+int(d[12]))/hz
    except (FileNotFoundError,ProcessLookupError,PermissionError):pass
   peak=max(peak,rss)
   if rss>2800*1024**2:reason='group RSS2800MiB'
   if cpu>210:reason='group CPU210'
   if time.monotonic()-start>230:reason='wall230'
   if reason:os.killpg(proc.pid,signal.SIGKILL);break
   time.sleep(.04)
  code=proc.wait()
 r={'command':cmd,'exit_code':code,'reason':reason,'sampled_peak_group_rss':peak,'wall_seconds':time.monotonic()-start}
 (F/(mod+'.guard.json')).write_text(json.dumps(r,indent=2)+'\n');print(mod,code,flush=True)
 if code:sys.exit(code if code>0 else 128-code)
helper()
