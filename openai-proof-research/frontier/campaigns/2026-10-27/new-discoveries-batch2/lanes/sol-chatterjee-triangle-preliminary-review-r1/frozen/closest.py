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
for i in ['2312.16544','2503.11390','2410.11418','1909.10140']:
 get(i+'-abs.html','https://arxiv.org/abs/'+i)
 get(i+'.pdf','https://arxiv.org/pdf/'+i)
get('publications.html','https://mirkogiacchini.github.io/publications.html')
get('publisher.html','https://www.tandfonline.com/doi/full/10.1080/00031305.2025.2571183')
for repo,n,old in [('the-omega-institute/trureturing','omega','a5a8bcdf56019e58c398f6f6d27a3620b896d001'),('openai/math','openai','7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a')]:
 h=json.loads((S/(n+'-HEAD.json')).read_text())['sha']
 print(n,h)
 if h!=old:get(n+'-delta.json','https://api.github.com/repos/'+repo+'/compare/'+old+'...'+h)
 if n=='omega':
  for j,path in enumerate(['docs/develop/theory/KrasniqiBoundaryContact.md','Library/Analytic/krasniqi2026bernsteinboundary.md']):get('omega-body-'+str(j)+'.md','https://raw.githubusercontent.com/'+repo+'/'+h+'/'+path)
(P/'closest-http.json').write_text(json.dumps(log,indent=2));print(json.dumps(log,indent=2))
