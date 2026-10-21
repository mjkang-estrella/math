from pathlib import Path
import urllib.request,json,hashlib,subprocess
ROOT=Path(__file__).resolve().parents[1];d=ROOT/'private/primary';d.mkdir(exist_ok=True)
items=[('aog-v4','https://arxiv.org/pdf/1411.4613v4'),('harvey-olver-v2','https://arxiv.org/pdf/1307.2274v2')]
r=[]
for name,url in items:
 try:
  b=urllib.request.urlopen(url,timeout=40).read();assert b.startswith(b'%PDF')
  p=d/(name+'.pdf');p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(d/(name+'.txt'))],check=True)
  t=(d/(name+'.txt')).read_bytes()
  r.append({'name':name,'url':url,'pdf_bytes':len(b),'pdf_sha256':hashlib.sha256(b).hexdigest(),'text_bytes':len(t),'text_sha256':hashlib.sha256(t).hexdigest(),'lines':len(t.decode().splitlines())})
 except Exception as e:r.append({'name':name,'url':url,'error':str(e)})
(d/'receipts.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
