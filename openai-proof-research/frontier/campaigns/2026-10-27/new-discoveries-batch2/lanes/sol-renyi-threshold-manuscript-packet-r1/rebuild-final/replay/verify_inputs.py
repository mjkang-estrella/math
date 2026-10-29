import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent
base=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
def rev(p):
 g=p/'.git'
 if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 h=(g/'HEAD').read_text().strip()
 if h.startswith('ref: '):
  r=h[5:];f=g/r
  h=f.read_text().strip() if f.exists() else next(x.split()[0] for x in (g/'packed-refs').read_text().splitlines() if x.endswith(' '+r))
 return h
pins=json.loads((root/'pins.json').read_text())
assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
for p in pins['packages']:assert rev(Path(p['path']))==p['rev'],p['name']
inputs={'PROOF.md':'sol-fresh-source-discovery-r111/PROOF.md',
 'review.md':'sol-renyi-threshold-preliminary-review-r1/review.md',
 'arxiv-v3.html':'root-renyi-threshold-review-freeze-r1/arxiv-v3.html'}
rows=[]
for n,o in inputs.items():
 h=sha(root/'inputs'/n);assert h==sha(base/o)
 rows.append({'copy':'inputs/'+n,'original':str(base/o),'sha256':h})
assert rows[0]['sha256']=='ca72b385e83d919fbaa97af4d55f0e7d00e949c01c8c4af07fd93ef30fef977a'
print(json.dumps({'pins_verified':True,'inputs':rows},indent=2))
