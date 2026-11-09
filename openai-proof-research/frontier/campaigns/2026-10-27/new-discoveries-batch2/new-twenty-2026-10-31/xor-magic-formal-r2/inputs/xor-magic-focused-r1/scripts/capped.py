import os,sys,subprocess,resource,time,json,pathlib,signal
root=pathlib.Path(__file__).resolve().parent.parent
name=sys.argv[1];cmd=sys.argv[2:];env=dict(os.environ,MALLOC_ARENA_MAX='2',OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2',MKL_NUM_THREADS='2',PYTHONDONTWRITEBYTECODE='1',TMPDIR=str(root/'outputs'))
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);os.setsid()
t=time.monotonic();peak=0;reason=None
with (root/'logs'/(name+'.log')).open('w') as out:
 p=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,env=env,preexec_fn=limits)
 while p.poll() is None:
  try:
   txt=pathlib.Path(f'/proc/{p.pid}/smaps_rollup').read_text();rss=sum(int(l.split()[1]) for l in txt.splitlines() if l.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')))*1024;peak=max(peak,rss)
  except FileNotFoundError:pass
  if peak>6*1024**3:reason='private RSS cap'
  if time.monotonic()-t>140:reason='wall cap'
  if reason:os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 code=p.wait()
r=dict(command=cmd,returncode=code,wall_seconds=time.monotonic()-t,sampled_private_rss_peak_bytes=peak,killed_reason=reason,cpu_limit_seconds=120,wall_limit_seconds=140,cpus=2,address_space_GiB=64,private_rss_limit_GiB=6,sample_seconds=.1)
(root/'receipts'/(name+'.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));print((root/'logs'/(name+'.log')).read_text()[-2500:])
