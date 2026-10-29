from pathlib import Path
import urllib.request,hashlib,json,datetime
P=Path(__file__).resolve().parent;log=[]
urls=[('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('kunisky-abs.html','https://arxiv.org/abs/2605.02023'),('kunisky.html','https://arxiv.org/html/2605.02023'),('mulgund.html','https://arxiv.org/html/2607.14087'),('transport.html','https://arxiv.org/html/2607.23241')]
def get(name,url):
 row={'url':url,'file':'sources/'+name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:
   b=r.read(18000001)
   if len(b)>18000000:raise ValueError('18MB download cap')
   (P/'sources'/name).write_bytes(b);row.update(status=r.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:row['error']=repr(e)
 log.append(row);(P/'http.json').write_text(json.dumps(log,indent=2));print(row)
for name,url in urls:get(name,url)
f=P/'sources/omega-head.json'
if f.exists():
 head=json.loads(f.read_text())['sha'];get('omega-delta.json','https://api.github.com/repos/the-omega-institute/trureturing/compare/73a5033dd654a16a14fcd1b13277f1a03d81d826...'+head)
