"""Ordinary public GETs only; never retries access denials or uses credentials."""
from pathlib import Path
from urllib.request import urlopen, Request
from urllib.error import HTTPError
from datetime import datetime, timezone
import json, hashlib, concurrent.futures, subprocess
HERE=Path(__file__).resolve().parent
OUT=HERE/'sources'; OUT.mkdir(exist_ok=True)
JOBS=[
 ('postnikov.pdf','https://math.mit.edu/~apost/papers/permutohedron.pdf'),
 ('postnikov-published.pdf','https://sites.math.washington.edu/~billey/classes/Hopf.algebra/bulletins/postnikov.2009.pdf'),
 ('an-abs.html','https://arxiv.org/abs/0807.3580'),
 ('an-primary.pdf','https://arxiv.org/pdf/0807.3580v2'),
 ('journal.html','https://www.sciencedirect.com/science/article/pii/S0021869309006772'),
 ('crossref.json','https://api.crossref.org/works/10.1016/j.jalgebra.2009.12.014'),
 ('openalex.json','https://api.openalex.org/works/https://doi.org/10.1016/j.jalgebra.2009.12.014'),
 ('mathdb.html','https://mathdb.com/problem/381028'),
 ('ideosphere.html','https://ideosphere.ai/papers/zero-pattern-inner'),
 ('ideosphere.pdf','https://ideosphere.ai/papers/zero-pattern-inner-v1.pdf'),
]
def fetch(job):
 name,url=job; r={'name':name,'url':url,'accessed_utc':datetime.now(timezone.utc).isoformat()}
 try:
  with urlopen(Request(url,headers={'User-Agent':'Research review (ordinary public retrieval)'}),timeout=35) as s:
   data=s.read();r.update(status=s.status,final_url=s.url,content_type=s.headers.get('Content-Type'),bytes=len(data))
   (OUT/name).write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest()
   if data.startswith(b'%PDF'):
    p=subprocess.run(['pdftotext','-layout',str(OUT/name),str((OUT/name).with_suffix('.txt'))],capture_output=True,text=True);r['pdftotext_exit']=p.returncode
 except Exception as e:
  r['error']=str(e)
  if isinstance(e,HTTPError):r['status']=e.code
 return r
if __name__=='__main__':
 with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: results=list(pool.map(fetch,JOBS))
 (HERE/'access-log.json').write_text(json.dumps(results,indent=2)+'\n')
 for r in results:print(r['name'],r.get('status'),r.get('bytes'),r.get('error',''))
