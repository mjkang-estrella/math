import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,)*2)
import pathlib,json,hashlib,time,datetime,sys,urllib.request,urllib.error,concurrent.futures,html.parser,re,atexit
P=pathlib.Path(__file__).resolve().parent
start=time.monotonic(); token=str(time.time_ns()); code=0
h=lambda b:hashlib.sha256(b).hexdigest()
def write(name,b):
 q=(P/name).resolve();assert q.is_relative_to(P);q.parent.mkdir(exist_ok=True,parents=True);q.write_bytes(b if isinstance(b,bytes) else b.encode())
def jwrite(n,d):write(n,json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def receipt():jwrite('resources/'+token+'.json',{'argv':sys.argv,'exit':code,'wall_seconds':time.monotonic()-start,'affinity':list(os.sched_getaffinity(0)),'cpu_limit':120,'AS_limit':6*1024**3,'self_usage':list(resource.getrusage(resource.RUSAGE_SELF)),'children_usage':list(resource.getrusage(resource.RUSAGE_CHILDREN)),'telemetry_limit':'self and reaped-child high water only, not concurrent group peak; all thread futures joined'})
atexit.register(receipt)
class Parser(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ('script','style'):self.skip+=1
  if t in ('p','div','h1','h2','h3','section','tr'):self.parts.append('\n')
  if t=='math':self.parts.append(dict(a).get('alttext',''))
  if t=='img':self.parts.append(dict(a).get('alt',''))
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip:self.parts.append(d)
def fetch(pair):
 name,url=pair;rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET','read_depth':'acquired, not yet read'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'SourceReview/1.0'}),timeout=18) as r:b=r.read(12*1024**2);rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=h(b),content_type=r.headers.get('Content-Type'))
  write('sources/'+name,b)
  if b'<html' in b[:3000].lower() or b'<!doctype html' in b[:3000].lower():
   parser=Parser();parser.feed(b.decode('utf-8','replace'));write('texts/'+name+'.txt',''.join(parser.parts))
 except Exception as e:rec.update(error=repr(e),status=getattr(e,'code',None))
 jwrite('http/'+name+'.json',rec);return rec
try:
 if sys.argv[1]=='fetch':
  pairs=json.loads((P/sys.argv[2]).read_text())
  with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
   for rec in ex.map(fetch,pairs):print(json.dumps(rec))
 elif sys.argv[1]=='exec':exec((P/sys.argv[2]).read_text(),globals())
except BaseException:
 code=1;raise
