from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,subprocess
L=Path(__file__).resolve().parent
rows=[]
for ident in ['2410.19322','1910.00846']:
 url='https://arxiv.org/abs/'+ident
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent mathematical source review'}),timeout=25) as r:
   b=r.read(1500000);status=r.status;final=r.url
  p=L/'primary'/f'{ident}-current.html';p.parent.mkdir(exist_ok=True);p.write_bytes(b)
  h=hashlib.sha256(b).hexdigest();assert hashlib.sha256(p.read_bytes()).hexdigest()==h
  rows.append({'url':url,'final_url':final,'status':status,'sha256':h,'copy':str(p.relative_to(L)),'frozen_before_reading':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
 except Exception as e:
  rows.append({'url':url,'failure':repr(e),'retry':False})
(L/'retrieval.json').write_text(json.dumps(rows,indent=2)+'\n')
# Generate our own bounded page extraction from the already frozen source PDF.
pdf=L/'frozen/frozen/ref-2b366749d177-fullerenes.pdf'
subprocess.run(['pdftotext','-layout','-f','13','-l','13',str(pdf),str(L/'primary/source-page13.txt')],check=True)
print(json.dumps(rows))
