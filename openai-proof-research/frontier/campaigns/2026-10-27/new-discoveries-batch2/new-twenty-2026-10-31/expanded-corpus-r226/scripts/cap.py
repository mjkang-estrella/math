from pathlib import Path
import subprocess,sys,os,resource,time,json,signal
L=Path(__file__).resolve().parents[1]; name=sys.argv[1]; cmd=sys.argv[2:]
env=dict(os.environ,MALLOC_ARENA_MAX='2',OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2',MKL_NUM_THREADS='2',TMPDIR=str(L/'inputs'))
def pre():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
t=time.monotonic(); peak=0; why=None
with (L/'logs'/f'{name}.log').open('x') as f:
 p=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT,env=env,preexec_fn=pre,cwd=L)
 while p.poll() is None:
  try:
   rss=int(Path(f'/proc/{p.pid}/statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE');peak=max(peak,rss)
   if rss>6*1024**3:why='RSS'
  except FileNotFoundError:pass
  if time.monotonic()-t>140:why='wall'
  if why:os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 rc=p.wait()
(L/'logs'/f'{name}.receipt.json').write_text(json.dumps(dict(command=cmd,returncode=rc,wall=time.monotonic()-t,peak_sampled_rss=peak,killed=why),indent=2)+'\n')
print(name,rc,round(time.monotonic()-t,3),peak)
