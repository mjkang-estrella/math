from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import requests,json,hashlib
p=Path(__file__).resolve().parent
urls={
 'crossref':'https://api.crossref.org/works/10.1556/012.2018.55.2.1392',
 'openalex':'https://api.openalex.org/works/https://doi.org/10.1556/012.2018.55.2.1392',
 'publisher-html':'https://akjournals.com/view/journals/012/55/2/article-p174.xml',
 'publisher-pdf':'https://akjournals.com/downloadpdf/journals/012/55/2/article-p174.xml',
 'springer-metadata':'https://link.springer.com/article/10.1556/012.2018.55.2.1392',
}
def get(item):
 name,url=item
 try:
  r=requests.get(url,headers={'User-Agent':'Mozilla/5.0'},timeout=35)
  ext='.pdf' if r.content.startswith(b'%PDF') else '.json' if 'json' in r.headers.get('content-type','') else '.html'
  (p/(name+ext)).write_bytes(r.content)
  return {'name':name,'url':url,'status':r.status_code,'final_url':r.url,'type':r.headers.get('content-type'),'bytes':len(r.content),'sha256':hashlib.sha256(r.content).hexdigest(),'path':name+ext}
 except Exception as e:return {'name':name,'url':url,'error':str(e)}
with ThreadPoolExecutor(max_workers=5) as ex:out=list(ex.map(get,urls.items()))
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n')
for r in out: print(r['name'],r.get('status'),r.get('type'),r.get('bytes'))
