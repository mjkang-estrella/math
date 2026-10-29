from pathlib import Path
import urllib.request,json,hashlib,datetime
P=Path(__file__).resolve().parent
urls={'gamma':'https://arxiv.org/html/2502.08948v2','knot':'https://arxiv.org/html/2509.16868v1','banana':'https://arxiv.org/html/2503.16296v1','gamma_abs':'https://arxiv.org/abs/2502.08948','knot_abs':'https://arxiv.org/abs/2509.16868','banana_abs':'https://arxiv.org/abs/2503.16296','omega_head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai_head':'https://api.github.com/repos/openai/math/commits/HEAD'}
log=[]
for name,url in urls.items():
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit'}),timeout=25) as r: data=r.read(); status=r.status
  f=P/'sources'/(name+'.html' if 'arxiv' in url else name+'.json');f.write_bytes(data)
  log.append(dict(name=name,url=url,status=status,file=str(f.relative_to(P)),sha256=hashlib.sha256(data).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:log.append(dict(name=name,url=url,error=str(e)))
(P/'http.json').write_text(json.dumps(log,indent=2))
