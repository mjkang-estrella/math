import urllib.request, json, hashlib, datetime
from pathlib import Path
P=Path(__file__).parent
jobs=[('nla-index.md','https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/matrix-inequalities-and-norms/README.md'),('liu-cheng.html','https://www.sciencedirect.com/science/article/pii/S0024379526001047'),('nla-resolved.md','https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/RESOLVED.md')]
r=[]
for name,url in jobs:
 e={'file':'sources/'+name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as q: b=q.read(); e['status']=q.status
  (P/e['file']).write_bytes(b);e.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as x:e['error']=str(x)
 r.append(e)
(P/'retrievals.json').write_text(json.dumps(r,indent=2))
print(json.dumps(r,indent=2))
