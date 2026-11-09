from pathlib import Path
import urllib.request,urllib.error,hashlib,json,subprocess,sys
L=Path(__file__).resolve().parent
log=[]
for name,url in [
 ('1909.05422-abs','https://arxiv.org/abs/1909.05422'),
 ('man-search','https://export.arxiv.org/api/query?search_query=ti:Minimal_rank_of_universal_lattices&max_results=3'),
 ('1802.07811','https://arxiv.org/pdf/1802.07811'),
 ('2311.16660','https://arxiv.org/pdf/2311.16660')]:
 try:
  with urllib.request.urlopen(url,timeout=25) as r:
   data=r.read(12000000);status=r.status;ctype=r.headers.get('Content-Type','')
  p=L/'sources'/(name+('.pdf' if data.startswith(b'%PDF') else '.html'));p.write_bytes(data)
  log.append(dict(url=url,status=status,path=str(p.relative_to(L)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
  if data.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=25)
 except Exception as e:log.append(dict(url=url,error=repr(e)))
(L/'access.json').write_text(json.dumps(log,indent=2)+'\n');print(json.dumps(log,indent=2))
