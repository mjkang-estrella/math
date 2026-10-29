from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
L=Path(__file__).parent
sources=[('danchev','https://emis.de/ft/40453'),('generalizing','https://arxiv.org/pdf/1412.4359v2'),('units','https://publi.math.unideb.hu/paper/2073/download/'),('ster','https://www.sciencedirect.com/science/article/pii/S0024379518300223'),('matrix-sums','https://matstud.org.ua/ojs/index.php/matstud/article/download/123/61/')]
with (L/'http.jsonl').open('x') as log:
 for name,url in sources:
  row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   h=hashlib.sha256();n=0
   with urllib.request.urlopen(url,timeout=25) as r,(L/'inputs'/f'{name}-retained').open('wb') as out:
    row.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'))
    while b:=r.read(65536):out.write(b);h.update(b);n+=len(b)
   row.update(bytes=n,sha256=h.hexdigest())
   if 'pdf' in row.get('content_type',''):subprocess.run(['pdftotext','-layout',str(L/'inputs'/f'{name}-retained'),str(L/'inputs'/f'{name}-body.txt')],check=True)
  except Exception as e:row['error']=repr(e)
  log.write(json.dumps(row)+'\n');log.flush()
