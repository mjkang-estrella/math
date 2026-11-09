from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent
ids=['2306.09033v2','2410.23662v1','2408.07411v1','2606.18234v5','2311.09054v2','2510.23249v1','2509.17201v2','2408.04897v1','2505.02585v1','2502.05180v4','2302.03977v4','2604.05491v1','2409.07008v1','2508.10871v3','2602.15797v1','2610.19965v1']
for ident in ids:
 p=L/'sources'/f'{ident}.pdf'
 if p.exists():continue
 u='https://arxiv.org/pdf/'+ident
 row=dict(url=u,at=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(u,timeout=22) as f:
   d=f.read(8000000);row['status']=f.status
  if not d.startswith(b'%PDF'):raise ValueError('not PDF; route parked')
  p.write_bytes(d);row.update(sha256=hashlib.sha256(d).hexdigest(),bytes=len(d))
  assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=20)
 except Exception as e:row['failure']=str(e)
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(ident,row.get('bytes'),row.get('failure'),flush=True)
