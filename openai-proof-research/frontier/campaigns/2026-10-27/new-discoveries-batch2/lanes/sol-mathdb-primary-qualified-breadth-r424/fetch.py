import urllib.request,urllib.error,json,hashlib,subprocess
from pathlib import Path
O=Path(__file__).parent; (O/'sources').mkdir(exist_ok=True); log=[]
for name,num in [('deformations',46033),('graphs',46037),('integration',46043),('prop',46056)]:
 url=f'https://ems.press/content/serial-article-files/{num}?nt=1'
 try:
  with urllib.request.urlopen(url,timeout=35) as r:
   b=r.read(); status=r.status
  assert b.startswith(b'%PDF')
  p=O/'sources'/f'{name}.pdf';p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  log.append({'url':url,'path':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'status':status})
 except Exception as e:
  log.append({'url':url,'error':str(e)}); print(log[-1])
  if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):break
(O/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
print(log)
