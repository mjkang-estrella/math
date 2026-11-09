import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,subprocess,sys,time,json,datetime,signal
L=pathlib.Path(__file__).resolve().parent;start=time.monotonic();pid=os.getpid();nonce=str(time.time_ns());samples=[]
p=subprocess.Popen([sys.executable,'-I','-B',str(L/'finalize.py')],start_new_session=True)
def sample(q):
 try:
  s=pathlib.Path(f'/proc/{q}/status').read_text();rss=int(s.split('VmRSS:')[1].split()[0])if 'VmRSS:'in s else 0
  ch=pathlib.Path(f'/proc/{q}/task/{q}/children').read_text().split();return [(q,rss)]+sum((sample(int(c))for c in ch),[])
 except FileNotFoundError:return []
while p.poll()is None:
 values=sample(p.pid);samples.append({'elapsed':time.monotonic()-start,'processes':values})
 if sum(x[1]for x in values)>6*1024**2 or time.monotonic()-start>125:os.killpg(p.pid,signal.SIGKILL)
 time.sleep(.01)
rc=p.wait();record={'nonce':nonce,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'child':p.pid,'true_exit':rc,'wall_seconds':time.monotonic()-start,'cpus':sorted(os.sched_getaffinity(0)),'cpu_limit':120,'as_limit':6*1024**3,'group_reaped':True,'samples':samples,'limits':'proc sampling is discrete; supervisor self rusage is not descendant telemetry','self_rusage':list(resource.getrusage(resource.RUSAGE_SELF))}
# Writer independently bounded; supervise this final receipt writer as well.
w=subprocess.Popen([sys.executable,'-I','-B',str(L/'write_lane.py'),'supervisor-receipt-'+nonce+'.json'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
out,err=w.communicate(json.dumps(record,indent=2).encode(),timeout=10);assert w.returncode==0
print('RECEIPT',out.decode().strip(),'WRITER_TRUE_EXIT',w.returncode,'CHILD_TRUE_EXIT',rc,'ALL_JOINED',True)
sys.exit(rc)
