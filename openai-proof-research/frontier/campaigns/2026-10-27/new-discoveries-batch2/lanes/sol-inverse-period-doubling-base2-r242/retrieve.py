from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
L=Path(__file__).resolve().parent
urls=[('logic.pdf','https://arxiv.org/pdf/1102.3698'),('current-search.xml','https://export.arxiv.org/api/query?search_query=all:%22period-doubling%22+AND+all:inverse&start=0&max_results=12')]
rows=[]
for name,url in urls:
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-research/1.0'}),timeout=35) as r:
   data=r.read(12000000);status=r.status;final=r.url
  p=L/'new-sources'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(data)
  rows.append({'url':url,'final':final,'status':status,'sha256':hashlib.sha256(data).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
  if name.endswith('.pdf'):subprocess.run(['pdftotext',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:rows.append({'url':url,'failure':repr(e),'no_retry':True})
(L/'retrieval.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
