from pathlib import Path
import urllib.request,json,hashlib,subprocess
O=Path(__file__).parent;(O/'primary').mkdir(exist_ok=True);out=[]
for year,num in [(2012,24),(2012,25),(2012,31),(2012,35),(2012,19),(2011,53)]:
 url=f'https://ems.press/doi/pdf/10.4171/OWR/{year}/{num}'; p=O/'primary'/f'{year}-{num}.pdf'
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read(8000000);status=r.status
  p.write_bytes(b);out.append({'url':url,'path':str(p.relative_to(O)),'status':status,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:
  out.append({'url':url,'failure':str(e)})
  if any(s in str(e) for s in ['403','429']):break
(O/'downloads.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
