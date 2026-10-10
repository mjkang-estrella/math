"""One-shot provenance writer; never used by the offline verifier."""
import json,hashlib,urllib.request,datetime,subprocess,concurrent.futures
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i69_global_algebra_rounding_budget/primary';S.mkdir(exist_ok=True)
assert not (S/'manifest.json').exists()
ids={'fox':'2004.12343','fox-sectional':'2211.01073','fox-steiner':'2205.08838','ppt':'quant-ph/0002089','kitaev':'2405.02434','bk':'2608.31000','bdhr':'1512.08031','cpv':'0810.0812','auddy':'2007.09024'}
urls=[(name+'-'+kind,'https://arxiv.org/'+kind+'/'+id) for name,id in ids.items() for kind in ['abs','pdf']]
urls += [('bds-pdf','https://rendiconti.dmi.units.it/volumi/54/017.pdf'),('poinsot-pdf','https://lipn.fr/~poinsot/Articles/Hilbertian_Frobenius_algebras_rev.pdf')]
def fetch(item):
 name,url=item; r={'name':name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=35) as f:
   b=f.read(); r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  ext='.pdf' if b.startswith(b'%PDF') else '.html';p=S/(name+ext);p.write_bytes(b);r.update(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if ext=='.pdf':
   q=p.with_suffix('.txt');z=subprocess.run(['pdftotext','-layout',str(p),str(q)],capture_output=True,text=True);r.update(text_path=str(q.relative_to(ROOT)),text_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),extract_returncode=z.returncode,extract_stderr=z.stderr)
 except Exception as e:r['error']=repr(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:r=list(ex.map(fetch,urls))
(S/'manifest.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps([{k:v for k,v in x.items() if k in ['name','status','error','extract_stderr']} for x in r],indent=2))
