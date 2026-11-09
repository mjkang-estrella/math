from pathlib import Path
import urllib.request,hashlib,json,subprocess
r=Path(__file__).resolve().parents[1]/'packet';rows=[]
for name,url in [('ruelle1970','https://www.ihes.fr/~ruelle/PUBLICATIONS/%5B28%5D.pdf'),('hjlp-v1','https://arxiv.org/pdf/2510.24825v1')]:
 try:
  b=urllib.request.urlopen(url,timeout=45).read();assert b.startswith(b'%PDF');p=r/'private/primary'/f'{name}.pdf';p.write_bytes(b);q=p.with_suffix('.txt');a=subprocess.run(['pdftotext','-layout',str(p),str(q)],capture_output=True,text=True,check=True)
  rows.append(dict(name=name,url=url,pdf=str(p.relative_to(r)),pdf_sha256=hashlib.sha256(b).hexdigest(),text=str(q.relative_to(r)),text_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),stderr=a.stderr));print(name,len(b),len(q.read_bytes()))
 except Exception as e:rows.append(dict(name=name,url=url,error=str(e)));print(name,'FAILED',str(e))
(r/'public/primary.json').write_text(json.dumps(rows,indent=2)+'\n')
