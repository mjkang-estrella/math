import os,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
import pathlib,json,hashlib,datetime,subprocess,time,threading,sys,urllib.request
P=pathlib.Path(__file__).resolve().parent
reads=[];jobs=[];http=[]
def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def read(f):
 f=pathlib.Path(f);b=f.read_bytes();reads.append(dict(path=str(f),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),utc=utc(),self_RSS_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss));return b
def job(argv,data=None):
 t=utc();q=subprocess.Popen(argv,stdin=subprocess.PIPE if data is not None else subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True);samples=[]
 def sample():
  while q.poll() is None:
   total=0
   for d in pathlib.Path('/proc').iterdir():
    if not d.name.isdigit():continue
    try:
     stat=(d/'stat').read_text().split();
     if int(stat[5])==q.pid:
      total+=int(stat[23])*os.sysconf('SC_PAGE_SIZE')
    except (OSError,ValueError,IndexError):pass
   samples.append(total)
   if total>6*1024**3: os.killpg(q.pid,9)
   time.sleep(.01)
 m=threading.Thread(target=sample);m.start()
 try:o,e=q.communicate(data,timeout=125)
 except subprocess.TimeoutExpired:
  os.killpg(q.pid,9);o,e=q.communicate()
 m.join();jobs.append(dict(argv=argv,start=t,end=utc(),exit=q.returncode,pid=q.pid,group_RSS_bytes=samples,reaped=True));
 if q.returncode:raise RuntimeError(e.decode())
 return o
def write(name,data):
 target=(P/name).resolve();assert target.is_relative_to(P) and not target.is_symlink()
 if not isinstance(data,str):data=json.dumps(data,indent=2,ensure_ascii=False)+'\n'
 job([sys.executable,'-I','-B',str(P/'write_lane.py'),name],data.encode())
def fetch(url,name):
 t=utc()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'SourceResearch/1.0'}),timeout=40) as z:b=z.read();status=z.status;final=z.url
  write(name,b.decode() if not name.endswith('.pdf') else __import__('base64').b64encode(b).decode())
  http.append(dict(url=url,start=t,end=utc(),status=status,final_url=final,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),artifact=name,encoding='base64' if name.endswith('.pdf') else 'utf8'))
  return b
 except Exception as e:http.append(dict(url=url,start=t,end=utc(),error=str(e)));return None
name=sys.argv[1]
try:exec(compile(sys.stdin.read(),'<research-input>','exec'))
finally:write('receipts/'+name+'.json',dict(utc=utc(),reads=reads,jobs=jobs,http=http,affinity=sorted(os.sched_getaffinity(0)),CPU=resource.getrlimit(resource.RLIMIT_CPU),AS=resource.getrlimit(resource.RLIMIT_AS),self_peak_RSS_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,limitation='Final receipt writer exit observed by parent but not recursively stored here. Top-level actual exit in tool receipt; no descendants except recorded jobs.'))
