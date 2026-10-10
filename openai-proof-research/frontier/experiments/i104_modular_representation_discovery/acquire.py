"""Preparation only; never imported by the final read-only verifier."""
from pathlib import Path
import concurrent.futures, hashlib, json, re, subprocess, urllib.request

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT/'frontier/sources/i104_modular_representation_discovery'
EXT = BASE/'external'
EXT.mkdir(exist_ok=True)
URLS = {
 'huang-yilmaz-v1.pdf': 'https://arxiv.org/pdf/2512.07369v1',
 'huang-yilmaz-author.pdf': 'https://yilmazdeniz.bilkent.edu.tr/papers/awc-galois-functorial.pdf',
 'huang-yilmaz-metadata.html': 'https://arxiv.org/abs/2512.07369',
 'ffz-blockwise-metadata.html': 'https://arxiv.org/abs/2512.15243',
 'ffz-blockwise-v1.pdf': 'https://arxiv.org/pdf/2512.15243v1',
 'coulembier-flake-published.html': 'https://link.springer.com/article/10.1007/s00029-026-01204-3',
 'kumar-survey.pdf': 'https://www.math.ucdavis.edu/~kapovich/EPR/eigensurvey2.pdf',
 'mathdb-search.html': 'https://mathdb.com/database?search=Alperin',
}

def fetch(item):
 name,url=item
 rec={'name':name,'url':url}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}), timeout=50) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  (EXT/name).write_bytes(data)
  rec.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  if name.endswith('.pdf'):
   assert data.startswith(b'%PDF'), 'not a PDF'
   out=EXT/(name+'.txt')
   p=subprocess.run(['pdftotext','-layout',str(EXT/name),str(out)],capture_output=True)
   rec.update(extraction={'command':['pdftotext','-layout',name,name+'.txt'],'returncode':p.returncode,'stderr':p.stderr.decode(),'sha256':hashlib.sha256(out.read_bytes()).hexdigest() if out.exists() else None})
 except Exception as e:rec['error']=repr(e)
 return rec

with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
 results=list(ex.map(fetch,URLS.items()))
(BASE/'retrievals.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ['name','status','bytes','error'] if k in r} for r in results]))
