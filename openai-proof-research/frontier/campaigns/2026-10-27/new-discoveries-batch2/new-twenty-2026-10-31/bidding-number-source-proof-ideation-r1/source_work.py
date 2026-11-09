import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,pathlib,json,hashlib,datetime,time,subprocess,urllib.request,io,threading
LANE=pathlib.Path(__file__).resolve().parent
WRITER=LANE/'write_lane.py'
def save(p,s):
 r=subprocess.run([sys.executable,'-I','-B',str(WRITER),p],input=s,text=True,capture_output=True,timeout=20);assert r.returncode==0,r.stderr
samples=[];stop=threading.Event()
def sample():
 while not stop.is_set():
  try:samples.append(int(next(x for x in pathlib.Path('/proc/self/status').read_text().splitlines() if x.startswith('VmRSS:')).split()[1]))
  except Exception:pass
  stop.wait(.02)
t=threading.Thread(target=sample);t.start();start=time.time();records=[]
try:
 if sys.argv[1]=='fetch':
  for name,url in [('classical.pdf','https://mathe2.uni-bayreuth.de/stoll/papers/games12.pdf'),('survey.pdf','https://library.slmath.org/books/Book71/files/GONC6-03.pdf'),('journal-record.html','https://livrepository.liverpool.ac.uk/3189414/')]:
   rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET'}
   try:
    with urllib.request.urlopen(url,timeout=25) as r:
     data=r.read(12000001);rec.update(status=r.status,final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());assert len(data)<=12000000
    if name.endswith('.pdf'):
     import pymupdf
     doc=pymupdf.open(stream=data,filetype='pdf');txt='\n'.join(f'PAGE {i+1}\n'+p.get_text() for i,p in enumerate(doc));save('sources/'+name+'.txt',txt)
    else:save('sources/'+name,data.decode('utf8',errors='replace'))
    rec['stored']='sources/'+name+('.txt' if name.endswith('.pdf') else '')
   except Exception as e:rec.update(error=repr(e),status=getattr(e,'code',None))
   records.append(rec)
  save('access.json',json.dumps(records,indent=2))
finally:
 stop.set();t.join();r=resource.getrusage(resource.RUSAGE_SELF);save('receipts/source-'+str(time.time_ns())+'.json',json.dumps({'start':start,'end':time.time(),'completed_finally':True,'cpu_self':r.ru_utime+r.ru_stime,'self_maxrss_kib':r.ru_maxrss,'sampled_self_rss_kib':max(samples,default=None),'samples':len(samples),'scope':'self only, no group/cgroup peak; writer children joined','limits':{'cpu_seconds':120,'as_bytes':6*1024**3,'allowed_cpus':list(os.sched_getaffinity(0))}},indent=2))
