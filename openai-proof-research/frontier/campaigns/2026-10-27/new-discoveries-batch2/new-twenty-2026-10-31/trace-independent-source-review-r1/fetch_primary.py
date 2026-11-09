from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import requests,datetime,json,hashlib
p=Path(__file__).parent
urls={
 'crossref':'https://api.crossref.org/works/10.1016/j.jalgebra.2012.02.025',
 'openalex':'https://api.openalex.org/works/https://doi.org/10.1016/j.jalgebra.2012.02.025',
 'palomar-hoge':'https://data.palomar-registry.org/api/v1/results?q=Hoge',
 'palomar-trace':'https://data.palomar-registry.org/api/v1/results?q=trace+reduction',
 'openai-head':'https://api.github.com/repos/openai/math/commits/main'}
def fetch(kv):
 k,u=kv;r={'name':k,'url':u,'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  x=requests.get(u,timeout=25);f=p/(k+'.body');f.write_bytes(x.content);r.update(status=x.status_code,final_url=x.url,sha256=hashlib.sha256(x.content).hexdigest(),file=f.name)
 except Exception as e:r['error']=str(e)
 return r
rs=list(ThreadPoolExecutor(max_workers=5).map(fetch,urls.items()));(p/'live-provenance.json').write_text(json.dumps(rs,indent=2));print(json.dumps(rs,indent=2))
for k in ['crossref','openalex']:
 try:
  j=json.loads((p/(k+'.body')).read_text());print(k, json.dumps(j.get('message',{}).get('link') if k=='crossref' else j.get('locations'),indent=2))
 except Exception as e:print(e)
