from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-stack-review-intake-r527'
def rec(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
m=json.loads((I/'manifest.json').read_bytes()); listed={x['path'] for x in m['files']}; actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert listed==actual
for x in m['files']:
 r=rec(I/x['path']);assert (r['size'],r['sha256'])==(x['size'],x['sha256'])
bind=json.loads((I/'bindings.json').read_bytes());out=[]
for x in bind:
 a=rec(Path(x['original']));b=rec(Path(x['copy']));assert (a['size'],a['sha256'])==(b['size'],b['sha256'])==(x['size'],x['sha256']);out.extend([a,b])
# Flat bindings, no content copies or upstream verifier execution.
for root in [L/'root-mathdb-accepted-exclusions-r304',L/'root-mathdb-cayley-review-intake-r363']:
 if root.exists():out.extend(rec(p) for p in root.rglob('*') if p.is_file())
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L.parents[3]/'sources/upstream.json',L.parents[3]/'sources/CONTENTS.md']:
 if p.is_file():out.append(rec(p))
(D/'flat-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
(D/'intake-check.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=len(listed),pairs=len(bind),ok=True),indent=2)+'\n')
print('Intake exact file set and direct pairs verified',len(listed),len(bind))
