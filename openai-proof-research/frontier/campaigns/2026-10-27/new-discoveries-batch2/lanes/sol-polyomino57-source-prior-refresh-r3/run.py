import os,sys,time,signal,subprocess,resource,json
from pathlib import Path
D=Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
signal.alarm(230)
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
p=subprocess.Popen([sys.executable,*sys.argv[1:]],start_new_session=True,env=env)
t=time.monotonic(); peak=0;reason=None
while p.poll() is None:
 rss=0
 for d in Path('/proc').iterdir():
  if d.name.isdigit():
   try:
    s=(d/'stat').read_text().split(') ',1)[1].split()
    if int(s[2])==p.pid:rss+=int(s[21])*os.sysconf('SC_PAGE_SIZE')
   except (OSError,ValueError,IndexError):pass
 peak=max(peak,rss)
 if rss>2800*1024**2 or time.monotonic()-t>225:
  reason='RSS or wall cap';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.045)
rc=p.wait();(D/('run-'+Path(sys.argv[1]).stem+'.json')).write_text(json.dumps(dict(exit=rc,seconds=time.monotonic()-t,sampled_peak_group_rss=peak,reason=reason,sample_seconds=.045)))
sys.exit(rc)
