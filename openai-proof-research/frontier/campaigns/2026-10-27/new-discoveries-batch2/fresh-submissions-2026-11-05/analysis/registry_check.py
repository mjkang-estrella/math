from pathlib import Path
import requests,json,hashlib
p=Path(__file__).parent;s=p/'sources';receipts=[]
for repo,branch in [('openai/math','4eaee87548250b2682affda7d05d947c05554bae'),('the-omega-institute/trureturing','5a97247bf6ad10485d8891db5430b9e34def4933')]:
 u=f'https://api.github.com/repos/{repo}/git/trees/{branch}?recursive=1';r=requests.get(u,timeout=40);f=s/(repo.split('/')[-1]+'-tree.json');f.write_bytes(r.content);d=r.json();hits=[x['path'] for x in d.get('tree',[]) if any(w in x['path'].lower() for w in ['korn','cummings','bernstein','lorton'])];receipts.append(dict(url=u,http_status=r.status_code,sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content),truncated=d.get('truncated'),entries=len(d.get('tree',[])),hits=hits))
(p/'registry-screen.json').write_text(json.dumps(receipts,indent=2));print(json.dumps(receipts,indent=2))
