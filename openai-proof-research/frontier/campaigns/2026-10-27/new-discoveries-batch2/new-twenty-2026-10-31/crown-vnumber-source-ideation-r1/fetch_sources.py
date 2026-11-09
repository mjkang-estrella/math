import resource,signal,os,pathlib,json,datetime,time,urllib.request,urllib.error,hashlib
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));signal.alarm(140);os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).resolve().parent;(p/'http').mkdir(exist_ok=True)
urls={
'current.abs':'https://arxiv.org/abs/2507.03889',
'nmsu.pdf':'https://math.nmsu.edu/research/summer-undergraduate-research-program/finished-papers/2024-REU-Crown_Graphs.pdf',
'liwski.html':'https://arxiv.org/html/2610.18213v1',
'domination.html':'https://link.springer.com/article/10.1007/s13348-023-00412-w',
'journal.html':'https://link.springer.com/article/10.1007/s10801-025-01464-w',
'openai.html':'https://github.com/openai/math',
'omega.html':'https://github.com/the-omega-institute/trureturing',
'pool.html':'https://github.com/LeanPool/lean-pool'}
from html.parser import HTMLParser
class Plain(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,d):self.parts.append(d)
def plain(data):
 h=Plain();h.feed(data.decode());return ' '.join(h.parts)
for name,url in urls.items():
 t=time.monotonic();r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=6) as f: data=f.read(16000001);r.update(status=f.status,final_url=f.url)
  if len(data)>16000000:raise ValueError('16MB cap exceeded')
  (p/'http'/name).write_bytes(data);r.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  if not name.endswith('.pdf'):(p/'http'/(name+'.txt')).write_text(plain(data))
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 r['wall_s']=time.monotonic()-t
 with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r))
with (p/'jobs.jsonl').open('a') as f:f.write(json.dumps({'job':'fetch_sources.py','pid':os.getpid(),'state':'completed synchronous','caps':'CPU120s AS6GiB wall140s affinity2; HTTP6s 16MB; sequential no children'})+'\n')
