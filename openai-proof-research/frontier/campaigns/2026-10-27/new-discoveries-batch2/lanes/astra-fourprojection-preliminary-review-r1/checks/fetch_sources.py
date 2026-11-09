from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import requests,hashlib,json,datetime,subprocess
B=Path(__file__).resolve().parents[1]; S=B/'sources'
items={
'arxiv-latest.html':'https://arxiv.org/abs/1602.04456',
'source-v3.pdf':'https://arxiv.org/pdf/1602.04456v3',
'publisher.html':'https://www.sciencedirect.com/science/article/pii/S019688581630077X',
'crossref.json':'https://api.crossref.org/works/10.1016/j.aam.2016.09.001',
'openalex.json':'https://api.openalex.org/works/https://doi.org/10.1016/j.aam.2016.09.001',
'hal-search.json':'https://api.archives-ouvertes.fr/search/?q=doiId_s:%2210.1016/j.aam.2016.09.001%22&fl=title_s,uri_s,fileMain_s,docType_s,version_i&wt=json',
'nechita-research.html':'https://nechita.net/research/',
'banica-home.html':'https://www.theodorbanica.com/',
'mathdb.json':'https://mathdb.com/api/posts/332493',
'sinkhorn.pdf':'https://arxiv.org/pdf/1911.04912',
'bipartite.pdf':'https://arxiv.org/pdf/1608.05811v2',
'weber.html':'https://link.springer.com/article/10.1007/s11785-023-01335-x',
'povm.pdf':'https://arxiv.org/pdf/2103.14126v2',
'brannan.pdf':'https://par.nsf.gov/servlets/purl/10185214',
'citers.json':'https://api.semanticscholar.org/graph/v1/paper/ARXIV:1602.04456/citations?fields=title,year,externalIds,url&limit=100',
}
def get(item):
 name,url=item;d=dict(file=name,url=url,accessed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  r=requests.get(url,timeout=35);(S/name).write_bytes(r.content);d.update(status=r.status_code,final_url=r.url,bytes=len(r.content),sha256=hashlib.sha256(r.content).hexdigest(),content_type=r.headers.get('content-type'))
  if r.content.startswith(b'%PDF'): subprocess.run(['pdftotext','-layout',str(S/name),str(S/name.replace('.pdf','.txt'))],check=True)
 except Exception as e:d['error']=str(e)
 return d
with ThreadPoolExecutor(max_workers=4) as ex: rows=list(ex.map(get,items.items()))
(S/'retrievals.json').write_text(json.dumps(rows,indent=2))
for x in rows:print(x['file'],x.get('status'),x.get('bytes'),x.get('error',''))
