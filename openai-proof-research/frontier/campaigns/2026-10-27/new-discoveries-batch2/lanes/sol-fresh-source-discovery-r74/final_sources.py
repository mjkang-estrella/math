import pathlib,json,urllib.request,datetime,hashlib,subprocess
from html.parser import HTMLParser
L=pathlib.Path(__file__).resolve().parent
rows=[]
for name,url in [('registry-chernoff.lean','https://raw.githubusercontent.com/the-omega-institute/trureturing/6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3/D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.lean'),('chernoff-new.pdf','https://arxiv.org/pdf/2607.18619v1')]:
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=20) as f:b=f.read(12000000);row.update(status=f.status,headers=dict(f.headers))
  (L/row['file']).write_bytes(b);row.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(L/row['file']),str(L/'sources'/name.replace('.pdf','.txt'))],check=True)
 except Exception as e:row['error']=str(e)
 rows.append(row)
(L/'http-final.json').write_text(json.dumps(rows,indent=2))
