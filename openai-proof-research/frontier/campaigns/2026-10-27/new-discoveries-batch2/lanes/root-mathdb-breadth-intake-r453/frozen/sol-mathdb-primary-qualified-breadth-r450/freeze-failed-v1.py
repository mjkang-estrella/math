import json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent
bindings={}; failures=[]
def bind(p,sha=None,size=None):
 p=pathlib.Path(p); b=p.read_bytes(); h=hashlib.sha256(b).hexdigest()
 if sha is not None and sha!=h: failures.append({'path':str(p),'issue':'hash mismatch','expected':sha,'actual':h})
 if size is not None and size!=len(b): failures.append({'path':str(p),'issue':'size mismatch'})
 bindings[str(p)]={'path':str(p),'sha256':h,'bytes':len(b)}
 return b
def load(p):return json.loads(bind(p))
for name in ['root-mathdb-breadth-intake-r449','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=B/name;m=load(d/'manifest.json')
 for f in m['files']:bind(d/f['path'],f['sha256'],f.get('size',f.get('bytes')))
 for r in load(d/'bindings.json'):
  c=pathlib.Path(r['copy']);c=c if c.is_absolute() else d/c
  bind(c,r['sha256'],r.get('size'))
  bind(r['original'],r['sha256'],r.get('size'))
I=B/'pi-mathdb-full-corpus-inventory-r301';m=load(I/'manifest.json')
chunks=[f for f in m['files'] if f['path'].startswith('corpus/') and f['path'].endswith('.jsonl')]
assert len(chunks)==20
for f in chunks:bind(I/f['path'],f['sha256'],f['bytes'])
# frozen_inputs are separately enumerated, not presumed payload members.
for f in m.get('frozen_inputs',[]):bind(I/f['path'],f['sha256'],f.get('bytes',f.get('size')))
for p in [B.parent/'ledger.json',B.parent/'prior-campaign-context.json',B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bind(p)
(L/'bindings.json').write_text(json.dumps(list(bindings.values()),indent=2)+'\n')
(L/'freeze-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'chunks_verified':len(chunks),'flat_references':len(bindings),'failures':failures,'scientific_content_read':False,'upstream_code_executed':False},indent=2)+'\n')
print(json.dumps({'files':len(bindings),'failures':failures},indent=2))
assert not failures
