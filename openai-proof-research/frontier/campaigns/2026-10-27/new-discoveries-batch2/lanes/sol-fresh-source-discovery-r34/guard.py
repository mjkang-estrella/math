import os,sys,time,subprocess,signal,json,resource
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(210,210))
from pathlib import Path
b=Path(__file__).resolve().parent;cmd=sys.argv[1:];start=time.monotonic();peak=0;reason=None
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
p=subprocess.Popen(cmd,cwd=b,env=env,start_new_session=True)
while p.poll() is None:
 rss=0
 for f in Path('/proc').glob('[0-9]*/stat'):
  try:
   s=f.read_text();v=s[s.rfind(')')+2:].split()
   if int(v[2])==p.pid:rss+=int(v[21])*os.sysconf('SC_PAGE_SIZE')
  except (OSError,ValueError,IndexError):pass
 peak=max(peak,rss)
 if rss>2800*1024*1024:reason='RSS ceiling'
 if time.monotonic()-start>60:reason='wall ceiling'
 if reason:os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.045)
rc=p.wait();r={'command':cmd,'returncode':rc,'kill_reason':reason,'wall_seconds':time.monotonic()-start,'sample_period_seconds':.045,'sampled_peak_process_group_RSS_bytes':peak,'ceiling_bytes':2800*1024*1024,'limits':'each child AS512MiB, own CPU/wall caps; BLAS1; serial'}
f=b/'guard-results.json';old=json.loads(f.read_text()) if f.exists() else [];old.append(r);f.write_text(json.dumps(old,indent=2));print(json.dumps(r));sys.exit(rc if rc else (1 if reason else 0))
