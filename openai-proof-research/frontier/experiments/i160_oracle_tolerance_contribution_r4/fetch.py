import urllib.request,hashlib,json,datetime,concurrent.futures
from pathlib import Path
S=Path('frontier/sources/i160_oracle_tolerance_contribution_r4/primary');S.mkdir(exist_ok=True)
urls={'inexact':'https://arxiv.org/abs/1710.00095v4','picard':'https://arxiv.org/abs/2609.06906v2','cloud':'https://arxiv.org/abs/2609.38710','stochastic':'https://proceedings.mlr.press/v336/chen26g.html','shifted1':'https://arxiv.org/abs/2311.14520','shifted3':'https://arxiv.org/abs/2412.17997','journal':'https://doi.org/10.1007/s10208-026-09753-x'}
def f(k,u):
 a=dict(name=k,url=u,time_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(u,timeout=25) as r:b=r.read();a.update(status=r.status,final_url=r.url)
  p=S/(k+'.html');p.write_bytes(b);a.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:a['error']=repr(e)
 return a
with concurrent.futures.ThreadPoolExecutor(max_workers=7) as ex:r=list(ex.map(lambda kv:f(*kv),urls.items()))
(S/'retrieval.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
