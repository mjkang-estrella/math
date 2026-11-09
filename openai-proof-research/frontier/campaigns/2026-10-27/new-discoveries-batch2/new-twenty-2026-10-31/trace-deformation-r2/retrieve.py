from pathlib import Path
import requests,json,hashlib,datetime,concurrent.futures
p=Path(__file__).parent;p.joinpath('sources').mkdir(exist_ok=True)
urls={'benanti-drensky':'https://arxiv.org/pdf/math/0701609v1','poisson':'https://arxiv.org/pdf/2402.06909','meir':'https://arxiv.org/pdf/2007.03845','palomar-head':'https://data.palomar-registry.org/browse/index.json','palomar-hoge':'https://data.palomar-registry.org/api/v1/results?q=Hoge','palomar-reduction':'https://data.palomar-registry.org/api/v1/results?q=trace+reduction','openai-head':'https://api.github.com/repos/openai/math/commits/main','hoge-abs':'https://arxiv.org/abs/1104.0904','author-page':'https://math.ruhr-uni-bochum.de/fakultaet/arbeitsbereiche/algebra/research-team-roehrle/team/dr-torsten-hoge/'}
def fetch(kv):
 k,u=kv
 try:
  r=requests.get(u,timeout=25);f=p/'sources'/(k+('.pdf' if r.content[:4]==b'%PDF' else '.body'));f.write_bytes(r.content)
  return {'name':k,'url':u,'final_url':r.url,'status':r.status_code,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':hashlib.sha256(r.content).hexdigest(),'bytes':len(r.content),'file':str(f)}
 except Exception as e:return {'name':k,'url':u,'error':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:r=list(ex.map(fetch,urls.items()))
(p/'source-provenance.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
