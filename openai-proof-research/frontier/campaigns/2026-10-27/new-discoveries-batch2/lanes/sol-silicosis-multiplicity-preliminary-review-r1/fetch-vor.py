import re,urllib.request,hashlib,json,datetime,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent
s=(O/'publisher.html').read_text();url=re.search(r'name="citation_pdf_url"\s+content="([^"]+)"',s)[1]
records=[]
for name,u in [('vor',url),('schoenberg-whitney','https://www.numdam.org/item/CM_1951__9__141_0.pdf')]:
 r=dict(url=u,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(u,timeout=25) as f:
   r.update(status=f.status,final_url=f.url,headers=dict(f.headers));h=hashlib.sha256();size=0
   with (O/(name+'.pdf')).open('wb') as g:
    while b:=f.read(65536):
     size+=len(b);assert size<20000000;g.write(b);h.update(b)
   r.update(bytes=size,sha256=h.hexdigest());subprocess.run(['pdftotext','-layout',str(O/(name+'.pdf')),str(O/(name+'.txt'))],check=True)
 except Exception as e:r['failure']=repr(e)
 records.append(r)
(O/'fetch-vor-records.json').write_text(json.dumps(records,indent=2));print(json.dumps(records,indent=2))
