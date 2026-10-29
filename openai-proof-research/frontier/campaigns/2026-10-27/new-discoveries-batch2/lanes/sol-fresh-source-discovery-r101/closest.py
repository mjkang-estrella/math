from pathlib import Path
import json,urllib.request,urllib.parse,hashlib,datetime,subprocess,re
P=Path(__file__).resolve().parent;log=json.loads((P/'http.json').read_text())
urls={'survey-current-abs.html':'https://arxiv.org/abs/2501.19385','survey-current.pdf':'https://arxiv.org/pdf/2501.19385','classical.pdf':'https://arxiv.org/pdf/2306.09965v2'}
t=json.loads((P/'registry-screen.json').read_text());h=t['heads']['omega'];root=P.parent/'root-edge-irregulator-final-freeze-r1'
for i,l in enumerate((root/'omega-tree.txt').read_text().splitlines()):
 path=l.split('\t')[-1]
 if ('GeneralPosition' in path or 'generalposition' in path) and (path.endswith('.md') or path.endswith('.lean')):urls['omega-relevant-'+str(i)+'.txt']='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+h+'/'+urllib.parse.quote(path)
for n,u in urls.items():
 try:
  with urllib.request.urlopen(u,timeout=20) as r:b=r.read();s=r.status
  (P/'sources'/n).write_bytes(b);log.append(dict(url=u,status=s,file='sources/'+n,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
  if n.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(P/'sources'/n),str(P/'sources'/n.replace('.pdf','.txt'))],check=True)
  print(n,s,len(b),flush=True)
 except Exception as e:log.append(dict(url=u,error=str(e)));print(n,e,flush=True)
(P/'http.json').write_text(json.dumps(log,indent=2))
