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
for i in ['1912.05118','2411.10302']:
 get(i+'-abs.html','https://arxiv.org/abs/'+i)
 get(i+'.pdf','https://arxiv.org/pdf/'+i)
h=json.loads((S/'omega-HEAD.json').read_text())['sha']
for j,f in enumerate(json.loads((S/'omega-delta.json').read_text())['files']):get('omega-new-body-'+str(j)+'.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/'+h+'/'+f['filename'])
(P/'additional-http.json').write_text(json.dumps(log,indent=2));print(json.dumps(log,indent=2))
