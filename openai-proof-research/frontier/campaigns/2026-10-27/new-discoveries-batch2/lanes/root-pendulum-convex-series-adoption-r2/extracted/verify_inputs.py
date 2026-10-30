import pathlib,json,hashlib
R=pathlib.Path(__file__).resolve().parent
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
assert sha(pathlib.Path(pins['lean_binary']))==pins['lean_sha256']
for p in pins['packages']:assert rev(pathlib.Path(p['path']))==p['rev'],p['name']
for row in json.loads((R/'originals-before.json').read_text()):assert sha(pathlib.Path(row['path']))==row['sha256'],row['path']
for row in json.loads((R/'input-records.json').read_text()):
 assert sha(R/row['copy'])==sha(pathlib.Path(row['original']))==row['sha256'],row
print(json.dumps({'pins_verified':len(pins['packages']),'frozen_entries_verified':len(json.loads((R/'originals-before.json').read_text())),'originals_and_copies_unchanged':True}))
