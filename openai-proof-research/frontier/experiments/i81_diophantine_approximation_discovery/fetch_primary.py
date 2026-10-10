"""Evidence acquisition only. Not called by offline verification."""
from pathlib import Path
import urllib.request, urllib.error, hashlib, json, datetime, subprocess
BASE=Path(__file__).resolve().parents[3]
S=BASE/'frontier/sources/i81_diophantine_approximation_discovery'
urls=[('zudilin-record.html','https://arxiv.org/abs/1507.05697'),('zudilin-v2.pdf','https://arxiv.org/pdf/1507.05697v2'),('eskandari-record.html','https://arxiv.org/abs/2609.26354'),('eskandari-v1.pdf','https://arxiv.org/pdf/2609.26354v1'),('cdt-record.html','https://arxiv.org/abs/2408.15403'),('cdt-icm.pdf','https://math.uchicago.edu/~fcale/papers/ICM.pdf'),('cdt-author.html','https://math.uchicago.edu/~fcale/research.html')]
(S/'primary').mkdir(exist_ok=True)
for name,url in urls:
 p=S/'primary'/name
 if p.exists():continue
 row={'url':url,'local':str(p.relative_to(BASE)),'captured':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I81 mathematics source comparison'}),timeout=45) as r:
   data=r.read(); row.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  p.write_bytes(data);row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  if data.startswith(b'%PDF'):
   t=p.with_suffix('.pdf.txt');res=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True,text=True)
   row['extraction']={'code':res.returncode,'stderr':res.stderr,'local':str(t.relative_to(BASE)),'sha256':hashlib.sha256(t.read_bytes()).hexdigest()}
 except Exception as ex:row['error']=repr(ex)
 with (S/'primary-requests.jsonl').open('a') as f:f.write(json.dumps(row,sort_keys=True)+'\n')
 print(name,row.get('status'),row.get('error',''))
