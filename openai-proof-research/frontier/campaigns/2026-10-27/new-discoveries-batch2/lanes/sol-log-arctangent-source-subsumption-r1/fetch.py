from pathlib import Path
import urllib.request,datetime,hashlib,json,re,concurrent.futures
D=Path(__file__).parent; (D/'live').mkdir(exist_ok=True)
jobs=[('openai-page','https://github.com/openai/math'),('omega-page','https://github.com/the-omega-institute/trureturing'),('count-page','https://github.com/suvrit/count-ex-machina'),('chen-ratio.pdf','https://rgmia.org/papers/v11n4/Gini-and-E-mean-Ratio.pdf'),('author-page','https://www.fer.unizg.hr/lenka.mihokovic')]
def fetch(job):
 n,u=job;r={'name':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=18) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/'live'/n).write_bytes(b)
  s=b.decode(errors='replace');r['currentOid']=list(dict.fromkeys(re.findall(r'"currentOid":"([0-9a-f]{40})"',s)))
 except Exception as e:r['failure']=str(e);r['action']='stop affected route; no retry'
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:out=list(ex.map(fetch,jobs))
(D/'live-retrievals.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
