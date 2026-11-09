from pathlib import Path
import requests,hashlib,json,subprocess
L=Path(__file__).resolve().parent
url='https://arxiv.org/pdf/2410.21651v1'
row={'url':url}
try:
 r=requests.get(url,timeout=30,allow_redirects=False);row.update(status=r.status_code,bytes=len(r.content))
 p=L/'2410.21651v1.pdf';p.write_bytes(r.content);row['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
 if r.status_code==200 and r.content.startswith(b'%PDF'):
  assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
  subprocess.run(['pdftotext','-layout',str(p),str(L/'2410.21651v1.txt')],check=True)
  row['text_sha256']=hashlib.sha256((L/'2410.21651v1.txt').read_bytes()).hexdigest()
except Exception as e:row['error']=str(e)
(L/'primary-followup.json').write_text(json.dumps(row,indent=2)+'\n');print(row)
