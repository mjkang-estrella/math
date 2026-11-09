from pathlib import Path
import urllib.request,hashlib,json,subprocess,datetime
L=Path(__file__).resolve().parent
row={'url':'https://arxiv.org/pdf/2101.12671v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retries':0}
try:
 with urllib.request.urlopen(row['url'],timeout=25) as f:
  row['status']=f.status;data=f.read(2000001)
 if len(data)>2000000 or not data.startswith(b'%PDF'):raise ValueError('oversized or non-PDF; parked')
 p=L/'retrieved'/'2101.12671v1.pdf';q=L/'frozen'/'live'/p.name;p.write_bytes(data);q.write_bytes(data)
 h=hashlib.sha256(data).hexdigest();assert h==hashlib.sha256(p.read_bytes()).hexdigest()==hashlib.sha256(q.read_bytes()).hexdigest()
 row.update(original=str(p),copy=str(q),sha256=h,bytes=len(data))
 t=L/'retrieved'/'2101.12671v1.txt';u=q.with_suffix('.txt')
 subprocess.run(['pdftotext','-layout',str(q),str(t)],check=True);u.write_bytes(t.read_bytes())
 row['text']={'original':str(t),'copy':str(u),'sha256':hashlib.sha256(t.read_bytes()).hexdigest()}
 assert row['text']['sha256']==hashlib.sha256(u.read_bytes()).hexdigest()
except Exception as e:row['failure']=str(e)
(L/'broader-access.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row,indent=2))
