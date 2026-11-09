from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess,concurrent.futures
R=Path(__file__).resolve().parents[1]
items=[('teyssier-v2','https://arxiv.org/pdf/2508.06770v2'),('feray-sniady-v4','https://arxiv.org/pdf/math/0701051v4'),('tensor-markov','https://par.nsf.gov/servlets/purl/10221127')]
def get(x):
 name,url=x;row=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  b=urllib.request.urlopen(url,timeout=30).read();assert b.startswith(b'%PDF');p=R/'packet/private/primary'/f'{name}.pdf';p.write_bytes(b);out=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(out)],check=True)
  row.update(size=len(b),sha256=hashlib.sha256(b).hexdigest(),text_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),status='acquired; not yet semantically read')
 except Exception as e:row['failure']=str(e)
 return row
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:rows=list(ex.map(get,items))
(R/'packet/private/primary/acquisition.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
