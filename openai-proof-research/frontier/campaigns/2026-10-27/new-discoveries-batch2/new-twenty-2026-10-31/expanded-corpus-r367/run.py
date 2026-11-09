import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,json,hashlib,subprocess,threading,time,datetime,urllib.request,urllib.error,base64
L=pathlib.Path(__file__).resolve().parent
stop=threading.Event(); peak=0; samples=0
# Includes current process and recursively live descendants. Sampled guard, not transient peak attestation.
def guard():
 global peak,samples
 while not stop.is_set():
  try:
   todo=[os.getpid()]; seen=set(); total=0
   while todo:
    pid=todo.pop()
    if pid in seen: continue
    seen.add(pid)
    try:
     st=pathlib.Path(f'/proc/{pid}/status').read_text(); total+=int(st.split('VmRSS:')[1].split()[0])*1024 if 'VmRSS:' in st else 0
     todo.extend(map(int,pathlib.Path(f'/proc/{pid}/task/{pid}/children').read_text().split()))
    except (OSError,ValueError): pass
   peak=max(peak,total); samples+=1
   if total>1536*1024**2:
    for pid in seen-{os.getpid()}:
     try: os.kill(pid,9)
     except OSError: pass
    os._exit(97)
  finally: stop.wait(.02)
g=threading.Thread(target=guard); g.start()
def write(name,s):
 p=subprocess.Popen([sys.executable,'-I','-B',str(L/'write_lane.py'),name],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 out,err=p.communicate(s,timeout=20)
 if p.returncode: raise RuntimeError((p.returncode,err))
def save(name,obj): write(name,json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
start=time.time(); tag=sys.argv[1]; exitcode=0
try:
 exec((L/(tag+'.py')).read_text(),globals())
except BaseException:
 exitcode=1
 import traceback; traceback.print_exc()
finally:
 save('resources-'+tag+'.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),elapsed=time.time()-start,affinity=sorted(os.sched_getaffinity(0)),cpu=resource.getrlimit(resource.RLIMIT_CPU),as_limit=resource.getrlimit(resource.RLIMIT_AS),rss_guard_bytes=1536*1024**2,sampled_tree_peak=peak,samples=samples,exit_code=exitcode,self_rusage=list(resource.getrusage(resource.RUSAGE_SELF)),reaped_children_rusage=list(resource.getrusage(resource.RUSAGE_CHILDREN)),limits='sampled live descendant RSS; not unsampled transient peak'))
 stop.set();g.join()
sys.exit(exitcode)
