import os,resource,subprocess,time,sys,pathlib,json,signal
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186'); (L/'logs').mkdir(exist_ok=True)
name=sys.argv[1]; log=L/'logs'/f'{name}.log'; rec=L/'logs'/f'{name}.receipt.json'
def pre():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0));os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
t=time.monotonic();peak=0;reason=None
with log.open('x') as f:
 p=subprocess.Popen(sys.argv[2:],cwd=L,stdout=f,stderr=subprocess.STDOUT,preexec_fn=pre,env={**os.environ,'MALLOC_ARENA_MAX':'2','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'2','TMPDIR':str(L/'tmp'),'PYTHONDONTWRITEBYTECODE':'1'})
 while p.poll() is None:
  rss=0
  for q in pathlib.Path('/proc').glob('[0-9]*'):
   try:
    stat=(q/'stat').read_text().split(') ',1)[1].split()
    if int(stat[2])==p.pid:
     rss+=int(next(x.split()[1] for x in (q/'status').read_text().splitlines() if x.startswith('VmRSS:')))*1024
   except (OSError,ValueError,StopIteration):pass
  peak=max(peak,rss)
  if rss>6*1024**3 or time.monotonic()-t>140:
   reason='RSS or wall cap';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 p.wait()
r={'command':sys.argv[2:],'returncode':p.returncode,'wall_seconds':time.monotonic()-t,'process_group_peak_rss_sampled':peak,'kill_reason':reason,'limits':'2 CPUs, CPU 120s, wall 140s, sampled group RSS 6 GiB, AS 12 GiB, MALLOC_ARENA_MAX=2'};rec.write_text(json.dumps(r,indent=2));print(json.dumps(r))
