from research import *
import subprocess
items=[('chen-liu-v1','https://arxiv.org/pdf/2610.06724v1'),('davison-mandel','https://d-nb.info/1243743123/34')]
r=[]
for name,url in items:
 try:
  b=urllib.request.urlopen(url,timeout=50).read();assert b[:4]==b'%PDF'
  p=PRIVATE/'primary'/(name+'.pdf');p.parent.mkdir(exist_ok=True);p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  r.append(dict(name=name,url=url,acquired_utc=now(),sha256=sha(b),text_sha256=sha(p.with_suffix('.txt').read_bytes()),bytes=len(b),status='acquired; later read extents separately'))
 except Exception as e:r.append(dict(name=name,url=url,utc=now(),failure=str(e)))
save('primary-acquisition.json',r);print(r)
