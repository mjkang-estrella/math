#!/usr/bin/env python3
"""Record remaining primary-access attempt and immutable version metadata."""
import urllib.request,hashlib,json,datetime,subprocess,concurrent.futures
from pathlib import Path
R=Path(__file__).resolve().parents[3];O=R/'frontier/sources/i15_odd_order_topology_resumed'
items=[('literature/conner-raymond.pdf','https://www.ams.org/journals/bull/1977-83-01/S0002-9904-1977-14179-7/S0002-9904-1977-14179-7.pdf')]
for a in ['2605.27537v1','2608.30620v1','2510.21550v1','2409.02220v1','2501.12512v2','2304.10399v3','0901.0442v2','2411.19400v2']:
 items.append(('metadata/arxiv-'+a+'.html','https://arxiv.org/abs/'+a))
def get(item):
 name,url=item;rec=dict(path=name,url=url,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=25) as f:b=f.read();rec.update(final_url=f.url,http_status=f.status)
  if name.endswith('.pdf'):assert b.startswith(b'%PDF'),'not PDF bytes'
  p=O/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if name.endswith('.pdf'):
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
   rec.update(text_path=str(p.with_suffix('.txt').relative_to(O)),text_sha256=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest())
 except Exception as e:rec['error']=str(e)
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:rs=list(ex.map(get,items))
(O/'additional-retrieval-manifest.json').write_text(json.dumps(rs,indent=2)+'\n');print(json.dumps(rs,indent=2))
