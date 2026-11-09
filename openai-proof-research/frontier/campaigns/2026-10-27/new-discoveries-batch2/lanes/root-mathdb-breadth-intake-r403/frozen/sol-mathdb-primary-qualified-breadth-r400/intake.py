exec(open(__file__.replace('intake.py','freeze.py')).read().split('paths=[]')[0])
R=L/'root-mathdb-breadth-intake-r399'; I=L/'pi-mathdb-full-corpus-inventory-r301'
def check(p,r):
 a=ref(p); assert a['sha256']==r['sha256'] and a['size']==r.get('size',r.get('bytes')),(str(p),'mismatch');return a
refs=[]
for r in json.loads((R/'manifest.json').read_text())['files']:refs.append(check(R/r['path'],r))
for r in json.loads((R/'bindings.json').read_text()):refs.append(check(Path(r['original']),r))
# Bind immediate referenced originals from historical binding files, without copying trees.
for p in [L/'root-mathdb-accepted-exclusions-r304/bindings.json',L/'root-mathdb-cayley-review-intake-r363/bindings.json']:
 if p.exists():
  for r in json.loads(p.read_text()):
   if 'original' in r:refs.append(ref(Path(r['original'])))
m=json.loads((I/'manifest.json').read_text());chunks=[r for r in m['files'] if r['path'].startswith('corpus/mathdb-normalized-chunk-') and r['path'].endswith('.jsonl')];print('chunks',len(chunks))
assert len(chunks)==20
for r in chunks:refs.append(check(I/r['path'],r))
# Bind actual history inputs from earlier flat refs (not content, no recursive copies).
p=L/'sol-mathdb-primary-qualified-breadth-r396/input-bindings.json'
data=json.loads(p.read_text())
def walk(v):
 if isinstance(v,dict):
  if 'sha256' in v:
   q=v.get('path') or v.get('original')
   if q and Path(q).is_file():refs.append(ref(Path(q)))
  for x in v.values():walk(x)
 elif isinstance(v,list):
  for x in v:walk(x)
walk(data)
f=O/'input-bindings.json'; assert not f.exists(); f.write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'refs':list({r['path']:r for r in refs}.values()),'chunks':[str(I/r['path']) for r in chunks]},indent=2)+'\n');f.chmod(0o444)
r=json.loads((R/'reserved-ids.json').read_text());c=json.loads((R/'coverage-delta.json').read_text()); ids=set(r['ids']);assert len(ids)==50 and r['lane']==O.name;assert len(c)==1383;assert not ids.intersection(map(int,c));assert not ids.intersection(r['other_active_reservations']);assert not ids.intersection([372627,372628,368940]);print('root manifest/originals/chunks verified; exact assignment and disjointness passed',len(refs))
