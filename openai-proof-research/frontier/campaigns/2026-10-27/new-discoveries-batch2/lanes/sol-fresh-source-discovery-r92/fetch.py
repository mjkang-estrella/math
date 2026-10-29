from pathlib import Path
import urllib.request,datetime,json,hashlib,subprocess
L=Path(__file__).resolve().parent
jobs={'plactic.pdf':'https://users.math.msu.edu/users/bsagan/Papers/Old/cpm-pub.pdf','short.pdf':'https://arxiv.org/pdf/2605.19979','inverse.pdf':'https://arxiv.org/pdf/2507.01332','properties.html':'https://link.springer.com/article/10.1007/s00233-026-10652-4','omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD'}
r=[]
for name,url in jobs.items():
 x={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(16000000);x.update(status=f.status,final_url=f.url)
  p=L/'sources'/name;p.write_bytes(b);x.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:x['error']=str(e)
 r.append(x)
(L/'http.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
