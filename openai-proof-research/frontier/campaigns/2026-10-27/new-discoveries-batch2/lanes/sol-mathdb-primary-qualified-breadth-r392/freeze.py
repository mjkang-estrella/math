import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent; R=B/'root-mathdb-breadth-intake-r391'; I=B/'pi-mathdb-full-corpus-inventory-r301'
def ref(p):
 p=pathlib.Path(p).resolve(); h=hashlib.sha256(); n=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''): h.update(b); n+=len(b)
 return dict(path=str(p),sha256=h.hexdigest(),size=n)
refs={}; checks=[]
def add(p,expected=None):
 r=ref(p); refs[r['path']]=r
 if expected: assert r['sha256']==expected['sha256'] and r['size']==expected.get('size',expected.get('bytes')),str(p)
for name in ['manifest.json','bindings.json','coverage-delta.json','queue.json','reserved-ids.json']:add(R/name)
for e in json.loads((R/'manifest.json').read_text())['files']:add(R/e['path'],e)
for e in json.loads((R/'bindings.json').read_text()):add(e['original'],e)
# Transitive metadata references only; never read scientific payload before sealed freeze.
p=B/'sol-mathdb-primary-qualified-breadth-r388/input-bindings.json'; j=json.loads(p.read_text())
def walk(x):
 if isinstance(x,dict):
  p=x.get('original',x.get('path'))
  if p and str(p).startswith('/') and 'sha256' in x:
   add(p,x)
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(j)
add(I/'manifest.json'); chunks=[e for e in json.loads((I/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/') and e['path'].endswith('.jsonl')];assert len(chunks)==20
for e in chunks:add(I/e['path'],e)
# Bind mandatory exclusions and Cayley dispositions, irrespective of inherited refs.
for lane in ['pi-mathdb-corpus-triage-r304','root-mathdb-cayley-review-intake-r363']:
 d=B/lane
 if d.exists():
  for p in d.iterdir():
   if p.is_file() and (p.suffix=='.json' or 'disposition' in p.name or 'exclusion' in p.name):add(p)
# r304 actual path resolved by directory names without content.
for d in B.glob('*r304'):
 for p in d.iterdir():
  if p.is_file() and ('exclusion' in p.name or 'disposition' in p.name):add(p)
out=dict(frozen_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),mode='flat immutable references; no corpus/history copies',refs=sorted(refs.values(),key=lambda x:x['path']),verified_corpus_chunks=20,root_manifest_verified_read_only=True)
p=L/'input-bindings.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');p.chmod(0o444)
print('FROZEN',len(refs),'refs; all20 chunks verified before content')
