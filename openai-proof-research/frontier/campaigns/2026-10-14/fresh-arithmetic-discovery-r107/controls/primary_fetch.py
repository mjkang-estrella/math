from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
ROOT=Path(__file__).resolve().parents[1]; d=ROOT/'private/primary';d.mkdir(exist_ok=True)
items=[('three-primes','https://mathweb.ucsd.edu/~ronspubs/pre_tres_egyptian.pdf'),('restricted-algorithm','https://personal.math.ubc.ca/~gerg/papers/downloads/AEFRRD.pdf'),('tenenbaum-yokota','https://tenenb.perso.math.cnrs.fr/PPP/Egyptian.pdf'),('elsholtz-odd-v1','https://arxiv.org/pdf/1606.02117v1')]
def get(item):
 name,url=item
 try:
  res=urllib.request.urlopen(url,timeout=35);b=res.read();assert b.startswith(b'%PDF')
  p=d/(name+'.pdf');p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=20)
  return dict(name=name,url=url,final_url=res.url,size=len(b),sha256=hashlib.sha256(b).hexdigest(),status='acquired',version='served PDF at retrieval; see body title/date')
 except Exception as e:return dict(name=name,url=url,status='failed',error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: records=list(ex.map(get,items))
(ROOT/'private/primary-metadata.json').write_text(json.dumps(records,indent=2)+'\n')
for r in records:print(r['name'],r['status'],r.get('error',''))
