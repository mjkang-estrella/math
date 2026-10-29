from pathlib import Path
import urllib.request,json,subprocess,datetime
P=Path(__file__).parent;S=P/'sources';log=[]
def get(n,u):
 try:
  with urllib.request.urlopen(u,timeout=30) as r:b=r.read(12000000)
  (S/n).write_bytes(b);log.append(dict(file=n,url=u,bytes=len(b),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
  if n.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(S/n),str(S/(n+'.txt'))],check=True)
  return b
 except Exception as e:log.append(dict(url=u,error=str(e)));return None
for n,u in [('chatterjee.pdf','https://mirkogiacchini.github.io/papers/cgk25_chatterjee_metricity.pdf')]+[(i+s,'https://arxiv.org/'+k+'/'+i) for i in ['2609.28707','2511.11901'] for s,k in [('-abs.html','abs'),('.pdf','pdf')]]:get(n,u)
for repo,n in [('the-omega-institute/trureturing','omega'),('openai/math','openai')]:get(n+'-HEAD.json','https://api.github.com/repos/'+repo+'/commits/HEAD')
(P/'http.json').write_text(json.dumps(log,indent=2));print(json.dumps(log,indent=2))
