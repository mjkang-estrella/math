import os,resource,pathlib,json,hashlib,urllib.request,urllib.error,datetime,concurrent.futures,time,sys
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
from html.parser import HTMLParser
p=pathlib.Path(__file__).parent
class Text(HTMLParser):
 def __init__(self): super().__init__(); self.out=[]
 def handle_starttag(self,t,a):
  if t in ['p','div','section','h1','h2','h3','li','tr']:self.out.append('\n')
  if t=='math':self.out.append(dict(a).get('alttext',''))
 def handle_data(self,d):self.out.append(d)
def fetch(item):
 key,url=item; start=time.monotonic();r={'key':key,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source review'}),timeout=18) as f:
   b=f.read(8*1024**2+1);assert len(b)<=8*1024**2;r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/'sources').mkdir(exist_ok=True);(p/'sources'/f'{key}.html').write_bytes(b)
   h=Text();h.feed(b.decode('utf-8',errors='replace'));(p/'sources'/f'{key}.txt').write_text(''.join(h.out))
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 r['elapsed_seconds']=time.monotonic()-start;return r
items=json.loads((p/sys.argv[1]).read_text())
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:res=list(ex.map(fetch,items))
with (p/'http-receipts.jsonl').open('a') as f:
 for r in res:f.write(json.dumps(r)+'\n');print(json.dumps(r))
print('TELEMETRY',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,sorted(os.sched_getaffinity(0)))
