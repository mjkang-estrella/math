from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import requests,json,hashlib
p=Path(__file__).resolve().parent/'sources'
urls={'2012.11018':'https://arxiv.org/pdf/2012.11018','2608.23006':'https://arxiv.org/pdf/2608.23006','349140-live':'https://mathdb.com/api/posts/349140','391922-live':'https://mathdb.com/api/posts/391922'}
def get(item):
 n,u=item
 try:
  r=requests.get(u,timeout=40,headers={'User-Agent':'Mozilla/5.0'});ext='.pdf' if r.content.startswith(b'%PDF') else '.json' if 'json' in r.headers.get('content-type','') else '.html';(p/(n+ext)).write_bytes(r.content)
  return {'url':u,'status':r.status_code,'file':n+ext,'bytes':len(r.content),'sha256':hashlib.sha256(r.content).hexdigest()}
 except Exception as e:return {'url':u,'error':str(e)}
with ThreadPoolExecutor(max_workers=4) as ex:res=list(ex.map(get,urls.items()))
(p/'receipts.json').write_text(json.dumps(res,indent=2)+'\n')
for r in res:print(r)
