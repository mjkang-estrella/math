import hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parent
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
pins=json.loads((R/'pins.json').read_text())
assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
base=Path(pins['packages'][0]['path']).parents[2]
assert sha(base/'lake-manifest.json')==pins['manifest_sha256']
for p in pins['packages']:assert rev(Path(p['path']))==p['rev'],p['name']
rows=json.loads((R/'frozen-before.json').read_text())
for row in rows:
 assert sha(Path(row['original']))==row['sha256'],row
 if 'copy' in row:assert sha(R/row['copy'])==row['sha256'],row
(R/'frozen-after.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({'pins_verified':True,'packages_verified':len(pins['packages']),
 'frozen_originals_and_copies_unchanged':True,'files':len(rows)}))
