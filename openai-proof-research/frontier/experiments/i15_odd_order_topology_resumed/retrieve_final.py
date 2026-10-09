#!/usr/bin/env python3
"""One bounded publisher-PDF access attempt; no authentication or paywall bypass."""
import datetime, hashlib, json, subprocess, urllib.request
from pathlib import Path
R=Path(__file__).resolve().parents[3]
O=R/'frontier/sources/i15_odd_order_topology_resumed'
url='https://link.springer.com/content/pdf/10.1007/BF01220468.pdf'
rec=dict(url=url,path='literature/raymond-scott-publisher.pdf',retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
try:
    with urllib.request.urlopen(url,timeout=25) as f:
        b=f.read();rec.update(final_url=f.url,http_status=f.status)
    assert b.startswith(b'%PDF'), 'not PDF bytes'
    p=O/rec['path'];p.write_bytes(b)
    rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
    subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
    rec.update(text_path=str(p.with_suffix('.txt').relative_to(O)),text_sha256=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest())
except Exception as e:
    rec['error']=str(e)
(O/'final-retrieval-manifest.json').write_text(json.dumps([rec],indent=2)+'\n')
print(json.dumps(rec))
