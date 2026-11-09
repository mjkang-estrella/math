from pathlib import Path
import sys,json,hashlib,shutil,zipfile
D=Path(sys.argv[1]).resolve();P=D.parent
# Make arithmetic reproduction portable within the extracted dossier.
p=D/'recompute.py';s=p.read_text().replace("D=Path(sys.argv[1]).resolve();P=D.parent;start=time.monotonic()", "D=Path(sys.argv[1]).resolve();P=D/'evidence';start=time.monotonic()")
s=s.replace("P/'percolation-formal-r8/normalized-trimmed.json'","D/'certificates/normalized-trimmed.json'").replace("P/'percolation-formal-r8/normalized.cnf'","D/'certificates/normalized.cnf'")
p.write_text(s)
(D/'certificates').mkdir(exist_ok=True)
for n in ['normalized-trimmed.json','normalized.cnf']:shutil.copyfile(P/'percolation-formal-r8'/n,D/'certificates'/n)
# Retain read source access receipts without performing any network requests.
extra=[]
for sub in ['arxiv-abs','publisher','triangle','arxiv-triangle-abs','openalex-work','openalex-citing']:
 extra.extend((P/'percolation-review-r1/downloads'/sub).glob('*'))
def h(f):return hashlib.sha256(f.read_bytes()).hexdigest()
pre={str(f):h(f) for f in extra};(D/'source-copy-inputs-before.json').write_text(json.dumps(pre,indent=2)+'\n')
for f in extra:
 out=D/'evidence'/f.relative_to(P);out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,out)
assert pre=={str(f):h(f) for f in extra}
(D/'source-copy-inputs-after.json').write_text(json.dumps(pre,indent=2)+'\n')
# Extract the MathDB entry by actual nested ID rather than treating the full multi-target result as this result.
j=json.loads((P/'expanded-corpus-r164/results.json').read_text());hits=[]
def walk(x):
 if isinstance(x,dict):
  if str(x.get('mathdb_id',x.get('id','')))=='333709':hits.append(x)
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(j);(D/'evidence/mathdb333709-discovery-results.json').write_text(json.dumps(hits,indent=2,ensure_ascii=False)+'\n')
# Source and packet inventories are separate from dossier artifact hashes.
source=[]
for f in (D/'evidence').rglob('*'):
 if f.is_file():source.append(dict(path=str(f.relative_to(D)),bytes=f.stat().st_size,sha256=h(f)))
(D/'source-copy-manifest.json').write_text(json.dumps(source,indent=2)+'\n')
# Remove superseded page renders; final renders remain.
for f in D.glob('qa-page-*.png'):f.unlink()
print('Dossier evidence staged; certificate data included; Lean packet remains external.')
