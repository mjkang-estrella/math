import urllib.request,pathlib,hashlib,json,datetime,subprocess
W=pathlib.Path(__file__).resolve().parent;p=W/'sources/pme-slides.pdf';u='https://www3.math.tu-berlin.de/numerik/spring10/JLV2.pdf';r=dict(url=u,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
try:
 with urllib.request.urlopen(u,timeout=25) as f:b=f.read(12000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 p.write_bytes(b);q=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,timeout=20);r.update(extraction_returncode=q.returncode,stderr=q.stderr.decode())
except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
(W/'sources/pme-slides.receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
