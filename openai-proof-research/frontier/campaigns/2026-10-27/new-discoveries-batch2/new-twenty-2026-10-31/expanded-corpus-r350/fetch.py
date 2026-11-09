import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,json,urllib.request,hashlib,datetime,time,concurrent.futures,html.parser,uuid
p=pathlib.Path(__file__).resolve().parent
start=time.monotonic();run=str(uuid.uuid4()); receipts=[]
class Parser(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0;self.links=[]
 def handle_starttag(self,t,a):
  d=dict(a)
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','li']:self.out.append('\n')
  if t=='img':self.out.append(d.get('alt',''))
  if t=='a' and d.get('href'):self.links.append(d['href'])
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip=max(0,self.skip-1)
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
def fetch(u):
 k=hashlib.sha256(u.encode()).hexdigest()[:16];r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET','key':k,'read_depth':'acquisition only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research source reader'}),timeout=20) as f:b=f.read(18000000);r.update(status=f.status,final_url=f.url)
  (p/'sources'/f'{k}.body').write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if not b.startswith(b'%PDF'):
   a=Parser();a.feed(b.decode('utf8','replace'));(p/'sources'/f'{k}.txt').write_text(''.join(a.out));r['links']=a.links
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 (p/'sources'/f'{k}.receipt.json').write_text(json.dumps(r,indent=2)+'\n');return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,sys.argv[1:]):receipts.append(r);print(json.dumps({k:v for k,v in r.items() if k!='links'}))
(p/f'resource-fetch-{run}.json').write_text(json.dumps({'exit':0,'wall_seconds':time.monotonic()-start,'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit':120,'AS':6*1024**3,'rusage':list(resource.getrusage(resource.RUSAGE_SELF)),'threads_reaped':True,'receipts':[r['key'] for r in receipts]})+'\n')
