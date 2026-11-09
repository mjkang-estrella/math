import pathlib,json,hashlib,urllib.request,subprocess,datetime
L=pathlib.Path(__file__).resolve().parent
url='https://arxiv.org/pdf/2203.17207v1';r=dict(family='threshold-corrected',url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat())
try:
 with urllib.request.urlopen(url,timeout=30) as f:data=f.read(12000000);r['status']=f.status
 if not data.startswith(b'%PDF'):raise ValueError('non-PDF, stop')
 p=L/'sources'/'2203.17207v1.pdf';p.write_bytes(data);r['pdf_sha256']=hashlib.sha256(data).hexdigest()
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 r['text_sha256']=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest()
except Exception as e:r['failure']=repr(e)
rows=json.loads((L/'access.json').read_text());rows.append(r);(L/'access.json').write_text(json.dumps(rows,indent=2)+'\n');print(r)
