import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,datetime,sys,time,urllib.request,urllib.error,re
from html.parser import HTMLParser
L=pathlib.Path(__file__).resolve().parent
S=L.parent/'expanded-corpus-r342'/'sources'
def write(n,s):
 p=(L/n).resolve();assert p.is_relative_to(L) and not p.is_symlink();p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def js(n,v):write(n,json.dumps(v,indent=2)+'\n')
class Txt(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,s):self.a.append(s)
def main():
 mode=sys.argv[1]
 if mode=='read':
  f=sys.argv[2];s=(S/f).read_text();start=int(sys.argv[3]);end=int(sys.argv[4]);print(s[start:end]);js('reads/'+str(time.time_ns())+'.json',{'path':str(S/f),'sha256':hashlib.sha256((S/f).read_bytes()).hexdigest(),'start':start,'end':end,'full_length':len(s)})
 elif mode=='locate':
  f=sys.argv[2];s=(S/f).read_text();print('length',len(s));
  for q in sys.argv[3:]:print(q,[(m.start(),s[max(0,m.start()-80):m.start()+150]) for m in list(re.finditer(re.escape(q),s))[:25]])
 elif mode=='fetch':
  url=sys.argv[2];name=sys.argv[3];rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET'}
  try:
   with urllib.request.urlopen(url,timeout=35) as r:b=r.read(12000000);rec.update(status=r.status,final_url=r.url)
   write('access/'+name,b.decode('utf-8',errors='replace'));rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),prefix=b[:100].hex())
  except urllib.error.HTTPError as e:
   b=e.read(4096);rec.update(status=e.code,error=str(e),bytes_prefix=len(b),prefix=b[:100].hex(),prefix_sha256=hashlib.sha256(b).hexdigest())
  except Exception as e:rec.update(error=repr(e))
  js('access/'+name+'.receipt.json',rec);print(json.dumps(rec))
 elif mode=='local':
  p=L/sys.argv[2];s=p.read_text();h=Txt();h.feed(s);s=' '.join(' '.join(h.a).split());write(sys.argv[2]+'.txt',s);print(s[:1000]);print('length',len(s))
 elif mode=='manifest':
  d={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','VERIFIED.json']};js('MANIFEST.json',d);bad=[n for n,h in d.items() if hashlib.sha256((L/n).read_bytes()).hexdigest()!=h];js('VERIFIED.json',{'count':len(d),'mismatches':bad});print(len(d),bad)
start=time.monotonic();code=0
try:main()
except BaseException:code=1;raise
finally:
 r=resource.getrusage(resource.RUSAGE_SELF);js('receipts/process-'+str(time.time_ns())+'.json',{'argv':sys.argv,'exit':code,'elapsed':time.monotonic()-start,'self_maxrss_kib':r.ru_maxrss,'self_user':r.ru_utime,'self_system':r.ru_stime,'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit':120,'as_limit':6*1024**3,'scope':'self only; not simultaneous group/cgroup peak'})
