import os,resource,time,json,hashlib,subprocess,pathlib,uuid,datetime
P=pathlib.Path(__file__).resolve().parent
reads=[];children=[];http=[];start=time.monotonic();uid=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S')+'-'+uuid.uuid4().hex[:8]
def sha(b): return hashlib.sha256(b).hexdigest()
def read(p):
 p=pathlib.Path(p); t=time.monotonic();b=p.read_bytes();reads.append({'path':str(p),'bytes':len(b),'sha256':sha(b),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_s':time.monotonic()-t,'depth':'full bytes acquired; semantic read separately recorded'});return b
def child(args,data):
 t=time.monotonic();p=subprocess.Popen(args,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE);peak=0
 import threading
 box={}
 def work():box['r']=p.communicate(data)
 th=threading.Thread(target=work);th.start()
 while th.is_alive():
  try:
   rss=int(pathlib.Path('/proc/'+str(p.pid)+'/status').read_text().split('VmRSS:')[1].split()[0]);peak=max(peak,rss)
   if rss>6*1024**2:p.kill()
  except (FileNotFoundError,IndexError):pass
  th.join(.01)
 th.join();out,err=box['r'];children.append({'argv':args,'exit':p.returncode,'sampled_direct_child_RSS_KiB':peak,'elapsed_s':time.monotonic()-t,'stderr':err.decode(errors='replace'),'descendants':'direct Python writer or pdftotext only; no grandchildren requested'});assert p.returncode==0,err;return out
def write(n,s):return child(['python3','-I','-B',str(P/'write_lane.py'),n],s.encode()).decode()
def save(n,obj):return write(n,json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def finish(extra=None):
 u=resource.getrusage(resource.RUSAGE_SELF);save('receipts/'+uid+'.json',{'uid':uid,'reads':reads,'children_before_receipt_writer':children.copy(),'http':http,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':120,'AS_limit':6*1024**3,'wall_cap_s':140,'self_RSS_KiB':u.ru_maxrss,'self_CPU_s':u.ru_utime+u.ru_stime,'elapsed_s':time.monotonic()-start,'exit_scope':'operation completed before receipt write; true process exit in external tool response','extra':extra,'receipt_writer':'writer exit captured in terminal harness, cannot embed own final exit without recursion'});print('RECEIPT',uid,'writer_exit',children[-1]['exit'])
