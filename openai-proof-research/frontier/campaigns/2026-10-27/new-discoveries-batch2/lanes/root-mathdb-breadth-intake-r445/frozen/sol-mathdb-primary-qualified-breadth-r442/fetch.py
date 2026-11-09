from pathlib import Path
import urllib.request,urllib.error,json,hashlib,re,datetime
R=Path(__file__).resolve().parent;(R/'sources').mkdir(exist_ok=True);out=[]
urls=[('owr2016-3','https://ems.press/journals/owr/articles/14211'),('owr2016-49','https://ems.press/journals/owr/articles/15170'),('owr2017-1','https://ems.press/journals/owr/articles/15206'),('owr2017-14','https://ems.press/journals/owr/articles/15219'),('owr2017-19','https://ems.press/journals/owr/articles/15427'),('owr2017-20','https://ems.press/journals/owr/articles/15428'),('equiangular','https://arxiv.org/pdf/1907.12466'),('cycles','https://arxiv.org/pdf/1512.00358'),('network','https://arxiv.org/pdf/1709.00707')]
for name,url in urls:
 e={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(12000000);e.update(status=f.status,final_url=f.url,content_type=f.headers.get('Content-Type'))
  p=R/'sources'/(name+('.pdf' if b.startswith(b'%PDF') else '.html'));p.write_bytes(b);e.update(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
  if p.suffix=='.html':print(name,'PDFLINKS',re.findall(r'[^"\s<>]*\.pdf[^"\s<>]*',b.decode(errors='replace'))[:10])
 except Exception as ex:e.update(error=str(ex))
 out.append(e);print(name,e.get('status',e.get('error')))
(R/'downloads.json').write_text(json.dumps(out,indent=2)+'\n')
