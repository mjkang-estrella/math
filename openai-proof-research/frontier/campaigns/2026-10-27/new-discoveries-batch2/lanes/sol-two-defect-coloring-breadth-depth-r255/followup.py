import pathlib,urllib.request,hashlib,json,subprocess,datetime
L=pathlib.Path(__file__).parent;u='https://arxiv.org/pdf/2608.10028v4';r={'url':u,'utc':str(datetime.datetime.now(datetime.timezone.utc))}
try:
 with urllib.request.urlopen(u,timeout=20) as f:b=f.read(3500001);assert len(b)<=3500000;r['status']=f.status
 p=L/'current'/'2608.10028v4.pdf';p.write_bytes(b);r['sha256']=hashlib.sha256(b).hexdigest();assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],check=True,timeout=12)
except Exception as e:r['failure']=repr(e)
(L/'followup-receipt.json').write_text(json.dumps(r,indent=2));print(r)
