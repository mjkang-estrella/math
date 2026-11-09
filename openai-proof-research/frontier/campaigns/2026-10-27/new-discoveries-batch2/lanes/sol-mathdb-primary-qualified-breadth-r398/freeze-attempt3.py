from pathlib import Path
import hashlib,json,datetime
O=Path(__file__).resolve().parent; B=O.parent; R=B/'root-mathdb-breadth-intake-r397'; C=B/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def ref(p):
 d=p.read_bytes();return dict(path=str(p.resolve()),size=len(d),sha256=hashlib.sha256(d).hexdigest())
refs={r['path']:r for r in load(O/'freeze-initial.json')['refs']}; checks=[]
def bind(p,expected=None):
 r=ref(p)
 if expected: assert r['sha256']==expected['sha256'] and r['size']==expected.get('size',expected.get('bytes')),str(p)
 refs[r['path']]=r
for lane in [R,B/'root-mathdb-accepted-exclusions-r304']:
 m=load(lane/'manifest.json')
 for f in (m['files'] if isinstance(m,dict) else m):bind(lane/f['path'],f if lane==R else None)
 bs=load(lane/'bindings.json')
 print('binding shape',lane.name,type(bs).__name__,list(bs)[:5] if isinstance(bs,dict) else len(bs))
 if isinstance(bs,list):
  for r in bs:bind(Path(r['original']),r);bind(lane/r['copy'],r)
 else:
  # Only inspect binding paths, never scientific summaries.
  def walk(v):
   if isinstance(v,dict):
    if 'original' in v:bind(Path(v['original']),v)
    for x in v.values():walk(x)
   elif isinstance(v,list):
    for x in v:walk(x)
  walk(bs)
chunks=[f for f in load(C/'manifest.json')['files'] if f['path'].startswith('corpus/')];assert len(chunks)==20
for f in chunks:bind(C/f['path'],f)
p=O/'input-bindings.json';assert not p.exists();p.write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),refs=sorted(refs.values(),key=lambda x:x['path']),verified_corpus_chunks=20,root_manifest_read_only_verified=True),indent=2)+'\n');p.chmod(0o444)
print('FROZEN AND VERIFIED',len(refs),'references; all twenty chunks in place')
for name in ['reserved-ids.json','queue.json','coverage-delta.json']:
 d=load(R/name);print(name, 'keys',list(d) if isinstance(d,dict) else 'list length '+str(len(d)))
print('reservations',json.dumps(load(R/'reserved-ids.json')))
print('r304 bindings',json.dumps(load(B/'root-mathdb-accepted-exclusions-r304/bindings.json')))
