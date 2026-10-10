"""Fresh bounded primary retrieval; failures retained; no overwrite."""
from pathlib import Path
import json,urllib.request,hashlib,datetime,subprocess,concurrent.futures
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i64_entropy_coefficient_extraction_novelty';D=S/'literature';D.mkdir(exist_ok=True)
old=json.loads((R/'frontier/sources/i61_averaged_entropy_coefficient_rounding/literature/manifest.json').read_text())
requests=[(x['name'],x['url']) for x in old]
requests += [('tropp-analysis','https://www.tropp.caltech.edu/notes/Tro22-Matrix-Analysis-LN.pdf'),('tropp-moments','https://tropp.caltech.edu/papers/Tro16-Second-Order-Matrix-preprint.pdf'),('noferini','https://eprints.maths.manchester.ac.uk/2462/1/gendk.pdf')]
for pin in json.loads((S/'pins.json').read_text()):
 if pin['path'].endswith(('06-linear-equality.tex','10_unital_averaging.tex','rigidity.tex','transport.tex')):requests.append(('raw-'+Path(pin['path']).stem,pin['url']))
def sha(b):return hashlib.sha256(b).hexdigest()
def fetch(pair):
 name,url=pair;row=dict(name=name,url=url,time_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I64 scholarly proof-operation review'}),timeout=35) as res:
   b=res.read();row.update(status=res.status,final_url=res.url,headers=dict(res.headers))
  ext='.pdf' if b.startswith(b'%PDF') else '.html' if b'<html' in b[:2000].lower() else '.tex' if name.startswith('raw-') else '.bin';p=D/(name+ext)
  with p.open('xb') as f:f.write(b)
  row.update(path=str(p.relative_to(R)),sha256=sha(b),bytes=len(b))
  if ext=='.pdf':
   cp=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True);t=D/(name+'.txt')
   with t.open('xb') as f:f.write(cp.stdout)
   row.update(text_path=str(t.relative_to(R)),text_sha256=sha(cp.stdout),pdftotext_stderr=cp.stderr.decode())
 except Exception as e: row['error']=repr(e)
 return row
assert not (D/'manifest.json').exists()
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:rows=list(ex.map(fetch,requests))
with (D/'manifest.json').open('x') as f:json.dump(rows,f,indent=2);f.write('\n')
print(json.dumps([dict(name=x['name'],status=x.get('status'),error=x.get('error')) for x in rows],indent=2))
