from pathlib import Path
import urllib.request,json,hashlib,subprocess
O=Path(__file__).parent;log=[]
for name,num in [('4133','46251'),('4426','46297'),('4411','46290')]:
 url='https://ems.press/content/serial-article-files/'+num+'?nt=1'
 try:
  with urllib.request.urlopen(url,timeout=30) as r:b=r.read(8000000)
  p=O/'primary'/(name+'.pdf');p.write_bytes(b);log.append({'url':url,'file':str(p.relative_to(O)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 except Exception as e:log.append({'url':url,'failure':repr(e),'retry':False})
for p in (O/'primary').glob('*.pdf'):
 r=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True);print(p.name,r.returncode,r.stderr.decode())
(O/'body-downloads.json').write_text(json.dumps(log,indent=2)+'\n')
