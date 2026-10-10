"""Capture public primary evidence; writes only the assigned I66 source directory."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import urllib.request, urllib.error, json, hashlib, datetime

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'frontier/sources/i66_dispersive_equation_discovery/primary'
OUT.mkdir(parents=True, exist_ok=True)
REQUESTS = [
 ('buck-abs', 'https://arxiv.org/abs/2609.23685'),
 ('buck-html', 'https://arxiv.org/html/2609.23685v1'),
 ('li-abs', 'https://arxiv.org/abs/2304.02078'),
 ('li-html', 'https://arxiv.org/html/2304.02078v2'),
 ('cao-abs', 'https://arxiv.org/abs/2410.04532'),
 ('cao-html', 'https://arxiv.org/html/2410.04532v1'),
 ('du-abs', 'https://arxiv.org/abs/1805.02775'),
 ('du-html', 'https://arxiv.org/html/1805.02775v2'),
 ('bhs-pdf', 'https://msp.org/apde/2020/13-2/apde-v13-n2-p03-p.pdf'),
 ('wallauch-abs', 'https://arxiv.org/abs/2006.04600'),
 ('wallauch-html', 'https://arxiv.org/html/2006.04600v2'),
]
def fetch(pair):
 name,url=pair
 rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0 (mathematics research; primary source verification)'})
  with urllib.request.urlopen(req,timeout=35) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  filename=name+('.pdf' if data.startswith(b'%PDF') else '.html')
  (OUT/filename).write_bytes(data)
  rec.update(file=filename,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 except Exception as e:
  rec['error']=repr(e)
  if isinstance(e,urllib.error.HTTPError):
   data=e.read();filename=name+'.error';(OUT/filename).write_bytes(data)
   rec.update(status=e.code,file=filename,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 return rec
if __name__=='__main__':
 with ThreadPoolExecutor(max_workers=6) as pool: records=list(pool.map(fetch,REQUESTS))
 (OUT/'responses.json').write_text(json.dumps(records,indent=2)+'\n')
 for rec in records: print(rec['name'],rec.get('status'),rec.get('bytes'),rec.get('error',''))
