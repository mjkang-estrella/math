import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,sys,re,time,hashlib,datetime
from html.parser import HTMLParser
L=pathlib.Path(__file__).resolve().parent; start=time.monotonic(); run=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
def write(rel,b):
 p=(L/rel).resolve(); assert p.is_relative_to(L); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(b)
class P(HTMLParser):
 def __init__(self): super().__init__(); self.out=[]; self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style','annotation']: self.skip+=1
  if t in ['p','div','section','h1','h2','h3','h4','li','tr']: self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style','annotation']: self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
code=0
try:
 name=sys.argv[1]; b=(L/'sources'/name).read_bytes(); p=P(); p.feed(b.decode()); text=re.sub('[ \t]+',' ',''.join(p.out)); text=re.sub('\n\s*\n+','\n',text); write('sources/'+name+'.txt',text)
 pats=sys.argv[2:]; excerpts=[]
 for pat in pats:
  for m in list(re.finditer(pat,text,re.I))[:2]:
   a=max(0,m.start()-550); z=min(len(text),m.end()+3500); excerpts.append(dict(pattern=pat,start=a,end=z,text=text[a:z]))
 write('read-excerpts/'+run+'.json',json.dumps(dict(source=name,sha256=hashlib.sha256(b).hexdigest(),excerpts=excerpts),indent=2)); print(json.dumps(excerpts,ensure_ascii=False))
except:code=1; raise
finally:
 u=resource.getrusage(resource.RUSAGE_SELF); write('receipts/process-inspect-'+run+'.json',json.dumps(dict(exit_code=code,wall_s=time.monotonic()-start,affinity=sorted(os.sched_getaffinity(0)),CPU_limit=120,AS_limit=6*1024**3,self_peak_RSS_KiB=u.ru_maxrss,self_CPU_s=u.ru_utime+u.ru_stime,external_wall_timeout=140,limitation='Self high-water, not sampled group peak')))
