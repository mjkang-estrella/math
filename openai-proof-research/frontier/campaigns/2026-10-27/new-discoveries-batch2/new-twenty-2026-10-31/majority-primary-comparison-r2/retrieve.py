from pathlib import Path
import requests,hashlib,json,datetime,concurrent.futures
P=Path(__file__).parent
jobs=[('caro-greedy-v1','https://arxiv.org/pdf/1010.2467v1'),('caro-directed-v1','https://arxiv.org/pdf/1010.2464v1')]
def fetch(j):
 n,u=j; t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  r=requests.get(u,timeout=45); b=r.content;(P/(n+'.body')).write_bytes(b)
  return dict(name=n,url=u,final_url=r.url,status=r.status_code,utc=t,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),content_type=r.headers.get('Content-Type'))
 except Exception as e:return dict(name=n,url=u,utc=t,error=str(e))
a=list(concurrent.futures.ThreadPoolExecutor(max_workers=2).map(fetch,jobs));(P/'retrieval-receipts.json').write_text(json.dumps(a,indent=2)); print(json.dumps(a,indent=2))
