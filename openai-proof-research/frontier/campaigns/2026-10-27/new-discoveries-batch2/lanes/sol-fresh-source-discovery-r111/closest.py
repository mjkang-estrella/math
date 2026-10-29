import urllib.request,hashlib,json,datetime,subprocess
from pathlib import Path
p=Path(__file__).parent/'sources'/'melbourne-tkocz.pdf';url='https://arxiv.org/pdf/2005.10930';h=hashlib.sha256();n=0
with urllib.request.urlopen(url,timeout=20) as r,p.open('wb') as f:
 for b in iter(lambda:r.read(65536),b''):f.write(b);h.update(b);n+=len(b)
print(json.dumps({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':r.status,'bytes':n,'sha256':h.hexdigest(),'pdftotext_exit':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],timeout=20).returncode}))
