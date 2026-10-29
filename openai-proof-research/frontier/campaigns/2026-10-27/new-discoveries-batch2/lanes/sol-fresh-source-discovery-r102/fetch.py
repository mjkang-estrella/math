from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
P=Path(__file__).resolve().parent;log=[]
urls={'wp.html':'https://arxiv.org/html/2605.14076','dom.html':'https://arxiv.org/html/2601.14494','forge.html':'https://arxiv.org/html/2609.03478','omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD'}
for n,u in urls.items():
 try:
  with urllib.request.urlopen(u,timeout=20) as r:b=r.read();s=r.status
  (P/'sources'/n).write_bytes(b);log.append(dict(url=u,status=s,file='sources/'+n,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));print(n,s,len(b),flush=True)
 except Exception as e:log.append(dict(url=u,error=str(e)));print(n,str(e),flush=True)
 (P/'http.json').write_text(json.dumps(log,indent=2))
