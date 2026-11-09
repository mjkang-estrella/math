import urllib.request,urllib.error,hashlib,json,datetime
from pathlib import Path
p=Path(__file__).resolve().parent
routes=[('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('chung-abs.html','https://arxiv.org/abs/2305.05130'),('brown-otto.pdf','https://arxiv.org/pdf/2008.01784')]
r=[]
for name,url in routes:
 d={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=22) as f:
   b=f.read(12000000); d.update(status=f.status,headers=dict(f.headers),sha256=hashlib.sha256(b).hexdigest(),file=name);(p/name).write_bytes(b)
   if 'head.json' in name:d['head']=json.loads(b)['sha']
 except Exception as e:d['error']=str(e)
 r.append(d);print({k:v for k,v in d.items() if k!='headers'},flush=True)
(p/'http-receipts.json').write_text(json.dumps(r,indent=2))
