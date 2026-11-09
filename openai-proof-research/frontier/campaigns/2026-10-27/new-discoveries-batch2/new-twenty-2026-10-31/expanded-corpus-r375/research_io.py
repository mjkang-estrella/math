import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,subprocess,time,json,hashlib,urllib.request,datetime,atexit,uuid,sys,threading
P=pathlib.Path(__file__).resolve().parent
RUN=uuid.uuid4().hex
EVENTS=[]
START=time.time()
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def read(f,depth='full acquisition'):
 f=pathlib.Path(f);b=f.read_bytes();EVENTS.append(dict(kind='read',path=str(f),utc=utc(),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),depth=depth));return b
def child(args,data=None):
 c=subprocess.Popen(args,stdin=subprocess.PIPE if data is not None else subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE);peak=0;samples=0
 result=[]
 def work():result.append(c.communicate(input=data))
 t=threading.Thread(target=work);t.start()
 while c.poll() is None:
  try:
   st=pathlib.Path('/proc/'+str(c.pid)+'/status').read_text();rss=int(st.split('VmRSS:')[1].split()[0]);peak=max(peak,rss);samples+=1
  except (FileNotFoundError,IndexError,ProcessLookupError):pass
  if peak>6*1024**2 or time.time()-START>130:c.kill()
  time.sleep(.005)
 t.join();out,err=result[0];code=c.wait();EVENTS.append(dict(kind='child',argv=args,utc=utc(),exit=code,sampled_RSS_KiB=peak,samples=samples,stderr=err.decode(errors='replace')));assert code==0,(args,err);return out
def write(name,obj):
 text=obj if isinstance(obj,str) else json.dumps(obj,indent=2,ensure_ascii=False)+'\n'
 child(['python3','-I','-B',str(P/'write_lane.py'),name],text.encode())
def fetch(url,name):
 e=dict(kind='http',url=url,utc=utc(),method='GET');b=b''
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'SourceResearch/1.0'}),timeout=25) as r:b=r.read();e.update(status=r.status,final_url=r.url)
 except Exception as ex:e.update(error=repr(ex))
 e.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());EVENTS.append(e)
 if b:
  # writer is text-only; PDFs preserved losslessly in base64 and decoded by pdftotext stdin
  if b.startswith(b'%PDF'):
   import base64
   write(name+'.pdf.base64',base64.b64encode(b).decode());out=child(['pdftotext','-layout','-','-'],b);write(name+'.txt',out.decode(errors='replace'))
  else:write(name+'.txt',b.decode(errors='replace'))
 return b
def finish():
 write('receipts/'+RUN+'.json',dict(run=RUN,start=START,end=time.time(),affinity=list(os.sched_getaffinity(0)),CPU_limit=120,AS_limit=6*1024**3,wall_limit=140,self_highwater_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,events=EVENTS,exit='normal interpreter shutdown; actual outer exit in tool receipt',limitation='No cgroup claims. Sampled child /proc RSS; self highwater distinct. Helper import read precedes helper receipt.'))
atexit.register(finish)
