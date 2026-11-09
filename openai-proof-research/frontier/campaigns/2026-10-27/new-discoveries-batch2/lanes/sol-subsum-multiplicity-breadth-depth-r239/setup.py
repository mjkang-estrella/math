from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).parent
B=L.parent.parent
R=L.parent/'sol-distance-centers-breadth-depth-r236'
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
L.joinpath('primary').mkdir(exist_ok=True)
admin=[]
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json']:
 d=p.read_bytes(); admin.append({'path':str(p),'sha256':h(p),'bytes':len(d)})
 if p.suffix=='.json':
  j=json.loads(d); print(p.name, list(j)[:30])
L.joinpath('administrative-snapshot.json').write_text(json.dumps(admin,indent=2))
bindings=[]
for p in [R/'SCOUTING.md',*sorted((R/'primary').glob('*'))]:
 if not p.is_file():continue
 # immutable reference, no recursive copying
 bindings.append({'original':str(p.resolve()),'sha256':h(p),'bytes':p.stat().st_size,'mode':'immutable-reference'})
L.joinpath('source-bindings.json').write_text(json.dumps(bindings,indent=2))
print((R/'SCOUTING.md').read_text())
print('PRIMARY NAMES', [p.name for p in (R/'primary').glob('*')])
assert all(h(Path(r['original']))==r['sha256'] for r in bindings)
