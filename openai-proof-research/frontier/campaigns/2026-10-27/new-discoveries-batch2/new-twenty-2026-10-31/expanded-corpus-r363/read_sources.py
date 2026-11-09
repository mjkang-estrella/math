import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,time,json,hashlib,subprocess,threading,datetime,urllib.request,urllib.error
from pathlib import Path
P=Path(__file__).resolve().parent
start=time.monotonic(); samples=[]; stop=threading.Event()
def sample():
 while not stop.wait(.05):
  try:
   s=Path('/proc/self/status').read_text();rss=int(s.split('VmRSS:')[1].split()[0]);samples.append(rss)
   if rss>5*1024**2:os._exit(97)
  except (OSError,IndexError):pass
t=threading.Thread(target=sample);t.start()
def write(n,s):
 r=subprocess.run([sys.executable,'-I','-B',str(P/'write_lane.py'),n],input=s,text=True,capture_output=True,timeout=20)
 assert r.returncode==0,r.stderr
 return {'path':n,'writer_exit':r.returncode,'bytes':len(s.encode()),'sha256':hashlib.sha256(s.encode()).hexdigest()}
def dump(n,v):return write(n,json.dumps(v,ensure_ascii=False,indent=2)+'\n')
try:
 from html.parser import HTMLParser
 class Parser(HTMLParser):
  def __init__(self):super().__init__();self.parts=[];self.skip=0
  def handle_starttag(self,tag,attrs):
   if tag in ['script','style']:self.skip+=1
   if tag in ['p','h1','h2','h3','h4','h5','h6','tr','li']:self.parts.append('\n')
  def handle_endtag(self,tag):
   if tag in ['script','style']:self.skip=max(0,self.skip-1)
  def handle_data(self,data):
   if not self.skip:self.parts.append(data)
 for ident in sys.argv[2:]:
  f=P/'sources'/(ident+'.html'); parser=Parser();parser.feed(f.read_text());lines=[' '.join(x.split()) for x in ''.join(parser.parts).splitlines() if x.strip()]; text='\n'.join(lines)+'\n';write('sources/'+ident+'.txt',text)
  print('SOURCE',ident,'LINES',len(lines))
  for i,l in enumerate(lines):
   if any(x in l.lower() for x in ['conjecture','definition 3.1','definition 50','definition 54','definition 57','min-entropy','max-intersection','example 4.17']):
    print('LINE',i+1,'\n','\n'.join(lines[max(0,i-2):i+6]))
finally:
 stop.set();t.join();u=resource.getrusage(resource.RUSAGE_SELF)
 dump('resource-'+str(time.time_ns())+'.json',{'argv':sys.argv,'wall_s':time.monotonic()-start,'self_CPU_s':u.ru_utime+u.ru_stime,'self_peak_RSS_KiB':u.ru_maxrss,'sampled_self_RSS_max_KiB':max(samples,default=None),'RSS_guard_KiB':5*1024**2,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit':120,'AS_limit':6*1024**3,'external_wall_cap':140,'scope':'self sampling; writer children joined, not group telemetry','exception':str(sys.exc_info()[1]) if sys.exc_info()[0] else None})
