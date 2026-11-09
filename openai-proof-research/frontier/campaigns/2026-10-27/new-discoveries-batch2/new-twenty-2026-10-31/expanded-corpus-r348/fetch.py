import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,urllib.request,hashlib,datetime,concurrent.futures,html.parser,sys,time
p=pathlib.Path(__file__).resolve().parent
class Parser(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','h4','li']:self.parts.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip:self.parts.append(d)
def fetch(pair):
 name,url=pair;r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'read_depth':'acquired only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=25) as f:b=f.read(12000000);r.update(status=f.status,final_url=f.url)
  r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),file='sources/'+name+'.html');(p/r['file']).write_bytes(b)
  q=Parser();q.feed(b.decode('utf-8',errors='replace'));(p/'sources'/ (name+'.txt')).write_text(''.join(q.parts))
 except Exception as e:r['error']=str(e)
 return r
pairs=json.loads(sys.argv[1]);start=time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:receipts=list(ex.map(fetch,pairs))
name='fetch-'+str(time.time_ns());(p/(name+'.json')).write_text(json.dumps({'receipts':receipts,'exit':0,'wall_s':time.monotonic()-start,'affinity':sorted(os.sched_getaffinity(0)),'usage':list(resource.getrusage(resource.RUSAGE_SELF)),'caps_before_reads':True,'threads_joined':True},indent=2)+'\n')
print(json.dumps(receipts))
