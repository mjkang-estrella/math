from pathlib import Path
import urllib.request,json,hashlib,datetime
P=Path(__file__).resolve().parent
urls={'super-abs':'https://arxiv.org/abs/1705.00928','super-pdf':'https://arxiv.org/pdf/1705.00928v2','super-domatic-search':'https://export.arxiv.org/api/query?search_query=ti:super+AND+ti:domatic&max_results=5','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head':'https://api.github.com/repos/openai/math/commits/HEAD'}
log=[]
for n,u in urls.items():
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'research-source-audit'}),timeout=25) as r:b=r.read();status=r.status
  f='sources/'+n+('.pdf' if n.endswith('pdf') else '.json' if n.endswith('head') else '.html');(P/f).write_bytes(b)
  log.append(dict(name=n,url=u,status=status,file=f,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:log.append(dict(name=n,url=u,error=str(e)))
(P/'http.json').write_text(json.dumps(log,indent=2));print(json.dumps(log,indent=2))
