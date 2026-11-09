from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import requests,datetime,json,hashlib
p=Path(__file__).parent
urls={
'palomar-kiraly':'https://data.palomar-registry.org/api/v1/results?q=Kiraly',
'openai-head':'https://api.github.com/repos/openai/math/commits/main',
'ppad':'https://egres.elte.hu/tr/egres-12-04.pdf',
'mpr-published':'https://dillon128.github.io/MPR19.pdf',
'openalex-mpr':'https://api.openalex.org/works/https://doi.org/10.37236/7947',
'openalex-cgt':'https://api.openalex.org/works/https://doi.org/10.1016/j.jctb.2008.09.005'}
def fetch(kv):
 k,u=kv;d={'name':k,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(u,timeout=20); (p/(k+'.body')).write_bytes(r.content);d.update(status=r.status_code,url_final=r.url,sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content))
 except Exception as e:d['error']=str(e)
 return d
r=list(ThreadPoolExecutor(max_workers=2).map(fetch,urls.items()));(p/'live-receipts.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
