from pathlib import Path
import os,sys,time,subprocess,resource,signal,json
w=Path(__file__).resolve().parent
os.chdir(w)
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
for n in ['tmp','cache','receipts']: (w/n).mkdir(exist_ok=True)
env=os.environ.copy()
env.update(MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1',TMPDIR=str(w/'tmp'),TMP=str(w/'tmp'),TEMP=str(w/'tmp'),XDG_CACHE_HOME=str(w/'tools/cache'),HOME=str(w/'tmp'))
label=sys.argv[1];cmd=sys.argv[2:]
def limits():
 os.setsid();resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
start=time.monotonic();p=subprocess.Popen(cmd,env=env,preexec_fn=limits);peak=0;reason=None
while p.poll() is None:
 rss=0
 for q in Path('/proc').glob('[0-9]*'):
  try:
   stat=(q/'stat').read_text().rsplit(')',1)[1].split()
   if int(stat[2])==p.pid:
    rss+=int((q/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
  except (OSError,ValueError,IndexError): pass
 peak=max(peak,rss)
 if rss>=6*1024**3 or time.monotonic()-start>138:
  reason='resource cap';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.1)
rc=p.wait()
r={'command':cmd,'exit_code':rc,'wall_seconds':round(time.monotonic()-start,3),'peak_sampled_rss_bytes':peak,'cpu_affinity':sorted(os.sched_getaffinity(0)),'cpu_limit_seconds':120,'wall_watchdog_seconds':138,'rss_limit_bytes':6*1024**3,'reason':reason}
(w/'receipts'/ (label+'.json')).write_text(json.dumps(r,indent=2)+'\n')
sys.exit(rc if rc>=0 else 128-rc)
