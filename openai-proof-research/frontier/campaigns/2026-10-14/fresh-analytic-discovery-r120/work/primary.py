from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
r=Path(__file__).resolve().parents[1]; specs=[('goww','https://arxiv.org/pdf/2104.11188v1'),('dlf','https://arxiv.org/pdf/2308.14660v2'),('ll','https://arxiv.org/pdf/0704.0808v1')]
def f(z):
 name,url=z;d={'id':name,'url':url};p=r/'packet/private/primary'/f'{name}.pdf'
 try:
  res=urllib.request.urlopen(url,timeout=50);b=res.read();assert b.startswith(b'%PDF');p.write_bytes(b);q=p.with_suffix('.txt');c=subprocess.run(['pdftotext','-layout',str(p),str(q)],capture_output=True,text=True,check=True);d.update(status='success',resolved=res.url,pdf='private/primary/'+p.name,text='private/primary/'+q.name,pdf_sha256=hashlib.sha256(b).hexdigest(),text_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),extraction_stderr=c.stderr)
 except Exception as e:d.update(status='failed',error=str(e))
 return d
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as e: ds=list(e.map(f,specs))
(r/'packet/public/primary-register.json').write_text(json.dumps(ds,indent=2)+'\n');print(ds)
