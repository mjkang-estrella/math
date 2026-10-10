"""Explicit acquisition only. Never called by the offline verifier."""
from pathlib import Path
import urllib.request, urllib.error, json, hashlib, datetime, subprocess
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i71_global_variation_algebra_rounding/primary'
S.mkdir(exist_ok=True)
if (S/'manifest.json').exists():
 raise SystemExit('Refusing to overwrite an existing acquisition manifest.')
requests=[('bk','2608.31000'),('li','1804.01358'),('hamiltonian','2605.26096'),('fox','2004.12343'),('auddy','2007.09024')]
manifest=[]
for name,aid in requests:
 for typ in ['abs','pdf']:
  url=f'https://arxiv.org/{typ}/{aid}'
  rec=dict(name=name+'-'+typ,url=url,time_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I71 mathematics research evidence capture'}),timeout=45) as f:
    body=f.read();rec.update(status=f.status,headers=dict(f.headers),final_url=f.url)
  except Exception as e:
   rec['error']=repr(e)
   if isinstance(e,urllib.error.HTTPError):
    body=e.read();q=S/(name+'-'+typ+'-failure.body');q.write_bytes(body)
    rec.update(path=str(q.relative_to(R)),sha256=hashlib.sha256(body).hexdigest())
   manifest.append(rec);continue
  q=S/(name+('.pdf' if typ=='pdf' else '-abs.html'));q.write_bytes(body)
  rec.update(path=str(q.relative_to(R)),sha256=hashlib.sha256(body).hexdigest(),bytes=len(body))
  if typ=='pdf':
   p=subprocess.run(['pdftotext','-layout',str(q),'-'],capture_output=True)
   z=q.with_suffix('.txt');z.write_bytes(p.stdout)
   rec.update(text_path=str(z.relative_to(R)),text_sha256=hashlib.sha256(p.stdout).hexdigest(),extract_status=p.returncode,extract_stderr=p.stderr.decode())
  manifest.append(rec)
  (S/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(S/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps([{'name':r['name'],'status':r.get('status'),'error':r.get('error')} for r in manifest],indent=2))
