import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,subprocess,threading,time,datetime,urllib.request,urllib.error
L=pathlib.Path(__file__).resolve().parent
rss=[]; stop=threading.Event()
def sample():
 while not stop.wait(.05):
  try: rss.append(int(pathlib.Path('/proc/self/status').read_text().split('VmRSS:')[1].split()[0]))
  except Exception: pass
thread=threading.Thread(target=sample);thread.start()
def sha(b): return hashlib.sha256(b).hexdigest()
def write(name,s):
 if not isinstance(s,str): s=json.dumps(s,indent=2,ensure_ascii=False)+'\n'
 r=subprocess.run(['timeout','15','python3','-I','-B',str(L/'write_lane.py'),name],input=s,text=True,capture_output=True,timeout=18)
 assert r.returncode==0,r.stderr
 return sha((L/name).read_bytes())
def finish(tag):
 stop.set();thread.join()
 write('resource-'+tag+'.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),affinity=sorted(os.sched_getaffinity(0)),cpu_limit=resource.getrlimit(resource.RLIMIT_CPU),as_limit=resource.getrlimit(resource.RLIMIT_AS),self_sampled_rss_kib=max(rss,default=0),self_ru_maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,scope='self sampled RSS only; not cgroup/process-group/transient peak',threads_joined=True,writer_children_reaped=True))
def fetch(url,name):
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'ResearchSourceReader/1.0'})
  with urllib.request.urlopen(req,timeout=22) as r: b=r.read(16000000);rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=sha(b))
  if b.startswith(b'%PDF'):
   import base64
   write(name+'.base64',base64.b64encode(b).decode())
   c=subprocess.run(['pdftotext','-layout','-','-'],input=b,capture_output=True,timeout=35)
   rec['pdftotext_exit']=c.returncode;write(name+'.txt',c.stdout.decode('utf-8',errors='replace'))
  else: write(name+'.txt',b.decode('utf-8',errors='replace'))
  rec['saved']=name;rec['read_depth']='acquired, not yet read'
 except Exception as e: rec['error']=str(e)
 return rec
