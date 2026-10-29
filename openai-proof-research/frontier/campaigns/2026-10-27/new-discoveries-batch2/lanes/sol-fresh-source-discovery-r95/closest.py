from pathlib import Path
import urllib.request,subprocess,json
P=Path(__file__).parent;out=[]
for name,url in [('hong-sharp-abs.html','https://arxiv.org/abs/2603.19646'),('hong-sharp.pdf','https://arxiv.org/pdf/2603.19646'),('tokmachev-page.html','https://www.mathnet.ru/eng/znsl7205')]:
 try:
  with urllib.request.urlopen(url,timeout=35) as r:b=r.read(8000000)
  (P/'sources'/name).write_bytes(b);out.append({'url':url,'file':name,'bytes':len(b)})
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(P/'sources'/name),str(P/'sources'/(name+'.txt'))],check=True)
 except Exception as e:out.append({'url':url,'error':str(e)})
(P/'closest-log.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
