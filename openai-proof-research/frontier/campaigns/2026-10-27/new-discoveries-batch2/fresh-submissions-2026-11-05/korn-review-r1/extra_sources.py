from pathlib import Path
import requests,json,hashlib,re,concurrent.futures
p=Path(__file__).parent;R=[]
jobs=[]
base=p.parent/'analysis/sources'
for x in json.loads((base/'trureturing-Library.json').read_text())['tree']:
 if x['type']=='blob' and re.search(r'korn|cummings|lorton|elastic|sobolev|trace|helmholtz|boundary|strain|feng',x['path'],re.I):jobs.append(('omega-'+hashlib.sha256(x['path'].encode()).hexdigest()[:10]+'.txt','https://raw.githubusercontent.com/the-omega-institute/trureturing/5a97247bf6ad10485d8891db5430b9e34def4933/Library/'+x['path']))
jobs += [('cummings-thesis-page.html','https://trace.tennessee.edu/entities/publication/3442b5ef-b55e-4ce8-a53a-cbf1decb554b'),('lorton-thesis-page.html','https://trace.tennessee.edu/entities/publication/c977f23b-f659-45f1-a571-0e52904563a9'),('feng-published-page.html','https://link.springer.com/article/10.1007/s10915-016-0219-4')]
def go(z):
 name,url=z
 try:
  q=requests.get(url,timeout=30);(p/'receipts'/name).write_bytes(q.content);return dict(url=url,status=q.status_code,file='receipts/'+name,sha256=hashlib.sha256(q.content).hexdigest())
 except Exception as e:return dict(url=url,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as e:R=list(e.map(go,jobs))
(p/'extra-source-receipts.json').write_text(json.dumps(R,indent=2));print('done',len(R))
