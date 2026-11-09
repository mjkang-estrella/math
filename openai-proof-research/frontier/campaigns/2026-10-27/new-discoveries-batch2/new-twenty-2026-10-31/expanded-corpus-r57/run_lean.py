import threading,signal
import os,pathlib,resource,subprocess,time,json,hashlib,sys
p=pathlib.Path(__file__).resolve().parent;root=pathlib.Path('/home/mj-kang/Documents/Dev/math');packages=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages';lean=root/'dlp-research/.tools/lean-4.34.1-linux/bin/lean'
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3));env=os.environ.copy();env['LEAN_PATH']=':'.join(str(x/'.lake/build/lib/lean') for x in packages.iterdir())
name=sys.argv[1] if len(sys.argv)>1 else 'Candidate';t=time.time()
with (p/(name+'.log')).open('w') as f:
 try:
  proc=subprocess.Popen([str(lean),'-DwarningAsError=true',str(p/(name+'.lean'))],stdout=f,stderr=subprocess.STDOUT,env=env,cwd=p,start_new_session=True)
  peak=0
  while proc.poll() is None:
   import psutil
   try:
    pp=psutil.Process(proc.pid);rss=sum(x.memory_info().rss for x in [pp]+pp.children(recursive=True));peak=max(peak,rss)
    if rss>6*1024**3 or time.time()-t>135:os.killpg(proc.pid,signal.SIGKILL)
   except psutil.NoSuchProcess:pass
   time.sleep(.05)
  code=proc.wait()
 except subprocess.TimeoutExpired:code='timeout'
(p/(name+'.run.json')).write_text(json.dumps(dict(exit=code,wall=time.time()-t,lean=str(lean),version=subprocess.check_output([str(lean),'--version'],text=True),lean_sha256=hashlib.sha256(lean.read_bytes()).hexdigest(),mathlib_revision='d13f23b723b8a846827a245b89c10fc7d3f11612',cpu_seconds=120,AS_GiB=64,RSS_limit_GiB=6,RSS_sample_ms=50,peak_RSS=peak,CPUs=sorted(os.sched_getaffinity(0)),full_upstream_rebuild=False),indent=2));print(code)
