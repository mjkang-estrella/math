import json,hashlib,zipfile,resource,signal,re
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(220)
D=Path(__file__).resolve().parent;A=D.parent/'root-polyomino57-full-formal-adoption-r1';bad=[]
ad=json.loads((A/'ADOPTION.json').read_text());m=json.loads((A/'source-manifest.json').read_text())
for p,v in ad['preserved_files'].items():
 b=(A/p).read_bytes()
 if len(b)!=v['bytes'] or hashlib.sha256(b).hexdigest()!=v['sha256']:bad.append(p)
with zipfile.ZipFile(A/'source-only-component.zip') as z:
 for p,v in m.items():
  b=z.read(p)
  if len(b)!=v['bytes'] or hashlib.sha256(b).hexdigest()!=v['sha256']:bad.append(p)
 w=z.read('formal/Witness.lean').decode();points={tuple(map(int,t)) for t in re.findall(r'\((-?\d+),(-?\d+)\)',w.split('def witness :')[0])}
 literal={(x,y) for x in range(-5,6) for y in range(-5,6) if abs(x)+abs(y)<=5 and (abs(x),abs(y))!=(2,2)}
 assert points==literal and len(points)==57
 inv=json.loads((A/'declaration-inventory.json').read_text());allowed={'propext','Classical.choice','Quot.sound'};exceptions=[]
 for row in inv:
  assert all(row.get(k) for k in ['origin','name','type','axioms','flags'])
  axs=set(row['axioms'].strip('[]').split(', '))-{''}
  if not axs<=allowed or 'unsafe=false' not in row['flags'] or 'axiom=false' not in row['flags']:bad.append(row['name'])
  if 'partial=true' in row['flags']:exceptions.append(row['name'])
 assert exceptions==['Polyomino57.attachCheck._unsafe_rec']
 out=dict(archive_manifest_entries=len(m),adoption_entries=len(ad['preserved_files']),declarations=len(inv),origins=len({r['origin'] for r in inv}),unique_names=len({r['name'] for r in inv}),nonempty_type_origin_axioms_flags=True,allowed_axioms=sorted(allowed),partial_exceptions=exceptions,witness_literal_equal=True,issues=bad,scope='Frozen byte/record audit only; no new Lean replay or full formal PASS.')
(D/'packet-audit.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
