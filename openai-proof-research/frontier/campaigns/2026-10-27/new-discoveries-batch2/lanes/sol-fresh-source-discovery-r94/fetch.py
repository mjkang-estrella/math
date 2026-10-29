from pathlib import Path
import urllib.request,json,hashlib,subprocess,datetime
p=Path(__file__).parent; rows=[]
urls={'bnt':'https://www.math.cmu.edu/~ttkocz/mypapers/mathematics/revent2.pdf','eg':'https://webusers.imj-prg.fr/~alexandros.eskenazis/Info-GM.pdf','luo':'https://arxiv.org/pdf/2609.11418','lt':'https://www.math.cmu.edu/~ttkocz/mypapers/mathematics/mom-ave.pdf','gmr':'https://arxiv.org/pdf/2608.00813'}
for key,url in urls.items():
 r={'key':key,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(6000000);r['status']=f.status
  (p/'sources'/f'{key}.pdf').write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'): subprocess.run(['pdftotext','-layout',str(p/'sources'/f'{key}.pdf'),str(p/'sources'/f'{key}.txt')],check=True)
 except Exception as e:r['error']=str(e)
 rows.append(r)
(p/'http.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
