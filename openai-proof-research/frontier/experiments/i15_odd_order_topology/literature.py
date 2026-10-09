#!/usr/bin/env python3
import urllib.request,hashlib,json,subprocess,datetime,concurrent.futures
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i15_odd_order_topology/literature'
items=[
 ('arabadji-baykur-v3','https://arxiv.org/pdf/2304.10399v3'),
 ('dovermann-schultz','https://math.ucr.edu/~res/inprogress/mid0614.pdf'),
 ('bak-morimoto','https://www.math.uni-bielefeld.de/~bak/bmsurg.pdf'),
 ('allender-boolean','https://people.cs.rutgers.edu/~allender/papers/csp.pdf')]
def get(item):
    name,url=item
    try:
        req=urllib.request.Request(url,headers={'User-Agent':'Research source verification'})
        with urllib.request.urlopen(req,timeout=45) as r: b=r.read(); final=r.url
        assert b.startswith(b'%PDF')
        p=OUT/(name+'.pdf'); p.write_bytes(b)
        subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
        return dict(name=name,url=url,final_url=final,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),text_sha256=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest(),retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    except Exception as e: return dict(name=name,url=url,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: data=list(ex.map(get,items))
(OUT/'new-manifest.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(data,indent=2))
