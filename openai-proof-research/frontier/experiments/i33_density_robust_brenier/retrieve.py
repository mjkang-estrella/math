"""Pin primary bytes, including errors; no writes outside the I33 source directory."""
from pathlib import Path
import concurrent.futures, datetime, hashlib, json, subprocess, urllib.request, urllib.error

ROOT = Path(__file__).resolve().parents[3]
DEST = ROOT / 'frontier/sources/i33_density_robust_brenier/literature'
ITEMS = [
 ('lm-current.html', 'https://arxiv.org/abs/2411.04908'),
 ('ruan-current.html', 'https://arxiv.org/abs/2610.07577'),
 ('wang-current.html', 'https://arxiv.org/abs/2610.09640'),
 ('lm-v3.pdf', 'https://arxiv.org/pdf/2411.04908v3'),
 ('ruan-v1.pdf', 'https://arxiv.org/pdf/2610.07577v1'),
 ('wang-v1.pdf', 'https://arxiv.org/pdf/2610.09640v1'),
 ('merigot-hal.html', 'https://hal.science/hal-05616391'),
 ('merigot.pdf', 'https://hal.science/hal-05616391/document'),
 ('dnwp-current.html', 'https://arxiv.org/abs/2404.02855'),
 ('dnwp-v1.pdf', 'https://arxiv.org/pdf/2404.02855v1'),
 ('letunstable.html', 'https://doi.org/10.5802/crmath.834'),
]

def get(item):
 name,url=item
 row={'url':url,'path':str((DEST/name).relative_to(ROOT)), 'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-provenance/1.0'}),timeout=40) as r:
   data=r.read(); row.update(status=r.status,final_url=r.url,headers=dict(r.headers))
 except urllib.error.HTTPError as e:
  data=e.read(); row.update(status=e.code,final_url=e.url,headers=dict(e.headers),error=str(e))
 except Exception as e:
  data=str(e).encode(); row.update(status=None,error=str(e))
 (DEST/name).write_bytes(data)
 row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 if data.startswith(b'%PDF'):
  out=DEST/(Path(name).stem+'.txt')
  run=subprocess.run(['pdftotext','-layout',str(DEST/name),str(out)],capture_output=True,text=True)
  row['extract_returncode']=run.returncode
  if out.exists(): row['extraction']={'path':str(out.relative_to(ROOT)),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'bytes':out.stat().st_size}
 return row

if __name__=='__main__':
 DEST.mkdir(parents=True,exist_ok=True)
 with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool: rows=list(pool.map(get,ITEMS))
 (DEST/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
 print(json.dumps([{k:r.get(k) for k in ('path','status','bytes','error')} for r in rows],indent=2))
