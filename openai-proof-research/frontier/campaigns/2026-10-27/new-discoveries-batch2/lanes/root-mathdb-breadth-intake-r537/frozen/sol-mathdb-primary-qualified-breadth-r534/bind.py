from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r533'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def info(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(p,e):
 a=info(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p);return a
out=[]
for p in I.rglob('*'):
 if p.is_file():out.append(info(p))
m=json.loads((I/'manifest.json').read_text());assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
for x in m['files']:check(I/x['path'],x)
for x in json.loads((I/'bindings.json').read_text()):
 for key in ('original','copy'):out.append(check(Path(x[key]),x))
m=json.loads((R/'manifest.json').read_text());print('r301 keys',list(m))
for x in m['files']+m['frozen_inputs']:
 if x['path'].startswith('corpus/') or x in m['frozen_inputs']:out.append(check(R/x['path'],x))
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json']+list((L/'root-mathdb-accepted-exclusions-r304').glob('*.json'))+list((L/'root-mathdb-cayley-decision-r363').glob('*')):
 if p.is_file():out.append(info(p))
(D/'flat-bindings.json').write_text(json.dumps(list({x['path']:x for x in out}.values()),indent=2)+'\n')
print('BOUND',len(out));print('corpus',sum('/corpus/' in x['path'] for x in out))
