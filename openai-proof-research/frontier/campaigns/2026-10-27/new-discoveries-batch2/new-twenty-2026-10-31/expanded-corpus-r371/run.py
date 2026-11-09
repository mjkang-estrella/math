import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,subprocess,time,json,pathlib,uuid,hashlib,datetime,threading
L=pathlib.Path(__file__).resolve().parent
code=sys.stdin.read(); tag=str(uuid.uuid4()); start=time.monotonic()
pre="""import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,hashlib,json,time,datetime,subprocess,sys,urllib.request,urllib.error,base64
L=pathlib.Path(__file__).resolve().parent if '__file__' in globals() else pathlib.Path(LANE)
reads=[]; http=[]
def read(p):
 p=pathlib.Path(p); t=time.monotonic(); b=p.read_bytes(); reads.append({'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'depth':'full bytes processed; semantic depth separately recorded','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seconds':time.monotonic()-t}); return b
def write(p,s):
 r=subprocess.run([sys.executable,'-I','-B',str(L/'write_lane.py'),p],input=s,text=True,capture_output=True,timeout=20); assert r.returncode==0,r.stderr
"""
pre=pre.replace("L=pathlib.Path(__file__).resolve().parent if '__file__' in globals() else pathlib.Path(LANE)","L=pathlib.Path("+repr(str(L))+")")
p=subprocess.Popen([sys.executable,'-I','-B','-c',pre+'\n'+code+'\nwrite("receipts/reads-'+tag+'.json",json.dumps({"reads":reads,"http":http},indent=2))'],stdin=subprocess.DEVNULL)
peak=0; samples=0; seen=set(); killed=False
while p.poll() is None:
 total=0; parents={p.pid}; changed=True; stats=[]
 for d in pathlib.Path('/proc').iterdir():
  if d.name.isdigit():
   try:
    v=(d/'stat').read_text().split(); stats.append((int(d.name),int(v[3]),int(v[23])*os.sysconf('SC_PAGE_SIZE')))
   except (OSError,ValueError,IndexError): pass
 while changed:
  changed=False
  for pid,ppid,rss in stats:
   if ppid in parents and pid not in parents: parents.add(pid);changed=True
 for pid,ppid,rss in stats:
  if pid in parents: total+=rss;seen.add(pid)
 peak=max(peak,total);samples+=1
 if total>6*1024**3 or time.monotonic()-start>125:
  killed=True
  for pid in parents:
   try: os.kill(pid,9)
   except ProcessLookupError: pass
 time.sleep(.01)
rc=p.wait(); u=resource.getrusage(resource.RUSAGE_CHILDREN)
r={'uuid':tag,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'true_worker_exit':rc,'wall_s':time.monotonic()-start,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':120,'AS_limit_bytes':6*1024**3,'sampled_descendant_peak_RSS_bytes':peak,'samples':samples,'pids':sorted(seen),'guard_killed':killed,'children_CPU_s':u.ru_utime+u.ru_stime,'sampling_limit':'10ms sampling can miss short processes; receipt-tail writer separately reported in stdout'}
w=subprocess.Popen([sys.executable,'-I','-B',str(L/'write_lane.py'),'receipts/process-'+tag+'.json'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True);w.stdin.write(json.dumps(r,indent=2));w.stdin.close();wp=0
while w.poll() is None:
 try: wp=max(wp,int(pathlib.Path('/proc/'+str(w.pid)+'/stat').read_text().split()[23])*os.sysconf('SC_PAGE_SIZE'))
 except (OSError,IndexError):pass
 time.sleep(.001)
w.wait();print(json.dumps({'process_receipt':tag,'exit':rc,'tail_writer_exit':w.returncode,'tail_writer_sampled_RSS':wp}),flush=True)
sys.exit(rc)
