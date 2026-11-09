from pathlib import Path
import urllib.request,subprocess,json,hashlib
O=Path(__file__).parent;out=[]
for name,url in [('mathias','https://math.berkeley.edu/~slaman/papers/Mathias_generics.pdf'),('ellipsoids','https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p05-p.pdf')]:
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read(8000000);status=r.status
  p=O/'primary'/f'{name}.pdf';p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  out.append({'url':url,'path':str(p.relative_to(O)),'status':status,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 except Exception as e:
  out.append({'url':url,'failure':str(e)})
  if '403' in str(e) or '429' in str(e):break
(O/'successor-downloads.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
