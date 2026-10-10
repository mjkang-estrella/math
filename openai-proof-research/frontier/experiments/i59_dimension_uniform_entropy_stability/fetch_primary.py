"""One-shot bounded primary capture; failures retained, no TLS bypass."""
from pathlib import Path
import urllib.request, urllib.error, json, hashlib, datetime, concurrent.futures, subprocess
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i59_dimension_uniform_entropy_stability/literature'
S.mkdir(parents=True,exist_ok=True)
if (S/'manifest.json').exists(): raise SystemExit('Refuse to overwrite original requests')
works={'fms':'2406.07406','mnr':'2309.01840','fk':'1008.4002','bk2026':'2608.31000','auddy':'2007.09024','bdhr':'1512.08031','bds':'2206.01521','epi':'1610.07969','kipp':'2411.08722','rad':'1404.5662'}
jobs=[(k+'-'+kind,'https://arxiv.org/'+kind+'/'+v) for k,v in works.items() for kind in ['abs','pdf']]
jobs += [('bds-journal','https://rendiconti.dmi.units.it/volumi/54/017.pdf'),('mnr-journal','https://perso.pages.math.cnrs.fr/users/cyril.roberto/Articles/Melbourne-Nayar-Roberto.pdf'),('mathdb','https://mathdb.com/database')]
def fetch(job):
 name,url=job; row=dict(name=name,url=url,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I59 mathematical primary-source research'}),timeout=40) as r:
   b=r.read(); row.update(status=r.status,final_url=r.url,headers=dict(r.headers))
 except urllib.error.HTTPError as e:
  b=e.read(); row.update(status=e.code,error=str(e))
 except Exception as e:
  row.update(status=None,error=repr(e)); return row
 ext='.pdf' if b.startswith(b'%PDF') else '.html'; p=S/(name+ext); p.write_bytes(b)
 row.update(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 if ext=='.pdf':
  t=p.with_suffix('.txt'); subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True)
  row.update(text_path=str(t.relative_to(ROOT)),text_sha256=hashlib.sha256(t.read_bytes()).hexdigest())
 return row
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool: rows=list(pool.map(fetch,jobs))
(S/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ['name','status','error'] if k in r} for r in rows]))
