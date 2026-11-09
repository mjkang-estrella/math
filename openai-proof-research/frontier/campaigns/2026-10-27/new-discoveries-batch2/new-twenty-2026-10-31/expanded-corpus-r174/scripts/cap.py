import os,sys,subprocess,time,signal,resource,json,pathlib
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
def setup():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120))
env=os.environ.copy();env.update(MALLOC_ARENA_MAX='2',OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='2',TMPDIR=str(L/'outputs'))
t=time.monotonic();p=subprocess.Popen(sys.argv[1:],preexec_fn=setup,env=env);peak=0;killed=None
while p.poll() is None:
 rss=0
 for q in pathlib.Path('/proc').iterdir():
  if not q.name.isdigit():continue
  try:
   s=(q/'stat').read_text().split()
   if int(s[4])==p.pid:rss+=int((q/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
  except (OSError,ValueError,IndexError):pass
 peak=max(peak,rss)
 if rss>6*1024**3 or time.monotonic()-t>140:
  killed='rss' if rss>6*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.2)
rc=p.wait()
with (L/'logs/resources.jsonl').open('a') as f:f.write(json.dumps(dict(argv=sys.argv[1:],returncode=rc,seconds=time.monotonic()-t,peak_group_rss=peak,killed=killed))+'\n')
sys.exit(rc if rc>=0 else 128-rc)
