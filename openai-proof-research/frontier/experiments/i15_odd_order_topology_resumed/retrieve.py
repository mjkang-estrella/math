#!/usr/bin/env python3
"""Explicit fresh retrieval; only resumed evidence. Verification does not run this."""
import urllib.request,hashlib,json,subprocess,datetime,concurrent.futures
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];OUT=ROOT/'frontier/sources/i15_odd_order_topology_resumed'
items=[
('literature/pesikoff-v1.pdf','https://arxiv.org/pdf/2605.27537v1'),
('literature/kremer-borel-v1.pdf','https://arxiv.org/pdf/2510.21550v1'),
('literature/kang-park-taniguchi-published.pdf','https://api.repository.cam.ac.uk/server/api/core/bitstreams/a132c5f8-d9d9-410a-abb9-33b5c8f14b83/content'),
('literature/raymond-scott.pdf','https://deepblue.lib.umich.edu/bitstream/2027.42/47327/1/13_2005_Article_BF01220468.pdf'),
('literature/lee-cyclic.pdf','https://people.math.harvard.edu/~slee/CyclicNielsen.pdf'),
('literature/kremer-2026-v1.pdf','https://arxiv.org/pdf/2608.30620v1'),
]
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
B='preprints/Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026/build/sections/'
MT='preprints/A-marked-tensor-obstruction-to-four-dimensional-disk-embedding-September-24-2026/build/sections/'
for p in [B+'chambers.tex',B+'formal.tex',B+'tensors.tex',B+'reflection.tex',B+'cyclic.tex',MT+'01-geometry.tex',MT+'04-algebraicity.tex',MT+'05-vertices.tex']:
 items.append(('upstream/'+p,'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+p))
def get(pair):
 name,url=pair; rec=dict(path=name,url=url)
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'})
  with urllib.request.urlopen(req,timeout=35) as res: b=res.read();rec.update(final_url=res.url,http_status=res.status)
  if name.endswith('.pdf'):assert b.startswith(b'%PDF'), 'not PDF bytes'
  p=OUT/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
  rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  if name.endswith('.pdf'):
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
   rec.update(text_path=str(p.with_suffix('.txt').relative_to(OUT)),text_sha256=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest())
  old=ROOT/'frontier/sources/i15_odd_order_topology'/name
  if old.exists():rec['matches_saved_i15']=old.read_bytes()==b
 except Exception as e:rec['error']=str(e)
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex: rows=list(ex.map(get,items))
(OUT/'retrieval-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
