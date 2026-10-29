from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
P=Path(__file__).resolve().parent;log=[]
urls={'primary-abs.html':'https://arxiv.org/abs/2404.19451','primary.pdf':'https://arxiv.org/pdf/2404.19451','published.pdf':'https://oro.open.ac.uk/98050/9/98050final.pdf','survey.pdf':'https://users.fmf.uni-lj.si/klavzar/preprints/2501.19385v2.pdf','sg-original.pdf':'https://www.numdam.org/item/10.1051/ro/2018003.pdf','sg-successor.pdf':'https://users.fmf.uni-lj.si/klavzar/preprints/sg%20cores%20Jul%202%20-%20revised.pdf','omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD'}
for n,u in urls.items():
 try:
  with urllib.request.urlopen(u,timeout=25) as r:b=r.read();s=r.status
  (P/'sources'/n).write_bytes(b);log.append(dict(url=u,status=s,file='sources/'+n,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
  if n.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(P/'sources'/n),str(P/'sources'/n.replace('.pdf','.txt'))],check=True)
  print(n,s,len(b),flush=True)
 except Exception as e:log.append(dict(url=u,error=str(e)));print(n,e,flush=True)
(P/'http.json').write_text(json.dumps(log,indent=2))
