from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent.parent; O=Path(__file__).resolve().parent; I=L/'root-mathdb-banzhaf-retirement-intake-r503'
def h(p):
 b=Path(p).read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def load(p):return json.loads(Path(p).read_text())
def write(n,x):(O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
binds=[h(p) for p in I.iterdir() if p.is_file()];write('initial-bindings.json',binds)
m=load(I/'manifest.json');actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()};expected={x['path'] for x in m['files']}|set(m['excluded_exact_paths']);assert actual==expected,(actual-expected,expected-actual)
for e in m['files']:
 a=h(I/e['path']);assert all(a[k]==e[k] for k in ('size','sha256')),e['path']
pairs=load(I/'bindings.json')
for e in pairs:
 for k in ('original','copy'):
  a=h(e[k]);assert all(a[t]==e[t] for t in ('size','sha256')),e[k]
refs=[L/'pi-mathdb-full-corpus-inventory-r301/manifest.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L.parents[4]/'sources/upstream.json',L.parents[4]/'sources/CONTENTS.md']
refs += list(L.glob('*r363/*decision*'))+list(L.glob('*r363/*DECISION*'))
write('flat-bindings.json',[h(p) for p in refs if p.exists()])
r=load(refs[0]);print('R301 SCHEMA',str(r)[:6500]);print('verified intake files',len(m['files']),'direct pairs',len(pairs));print('refs', [str(p) for p in refs])
