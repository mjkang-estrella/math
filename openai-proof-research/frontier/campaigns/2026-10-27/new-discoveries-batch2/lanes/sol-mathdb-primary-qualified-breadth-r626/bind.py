from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).resolve().parent; L=D.parent; B=L.parent
I=L/'root-mathdb-breadth-intake-r625'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
refs={}
def bind(p,sha=None,size=None):
 p=Path(p); b=p.read_bytes(); h=hashlib.sha256(b).hexdigest()
 if sha is not None: assert h==sha,(str(p),'hash')
 if size is not None: assert len(b)==size,(str(p),'size')
 refs[str(p)]={'path':str(p),'sha256':h,'size':len(b)}
 return b
bind(I/'manifest.json','db41d16843b88e3f88a803283128dba18df4e5cab5497964f4eb5e41500755fc',10061)
m=load(I/'manifest.json')
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
for x in m['files']:bind(I/x['path'],x['sha256'],x['size'])
bind(I/'verification-receipt.json','7f68a9cc178fdf83fbddcbeb1c09ad55599902e3e570f88fcf96b4c20519e4cc',1156)
for x in load(I/'bindings.json'):
 for k in ['original','copy']:bind(x[k],x['sha256'],x['bytes'])
cm=load(C/'manifest.json'); chunks=[x for x in cm['files'] if x['path'].startswith('corpus/')]
assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for x in chunks+cm['frozen_inputs']:bind(C/x['path'],x['sha256'],x['bytes'])
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md']:
 bind(p)
for x in load(I/'frozen/sol-mathdb-primary-qualified-breadth-r622/flat-bindings.json'):
 if any(t in x['path'] for t in ['root-mathdb-accepted-exclusions-r304/accepted','root-mathdb-accepted-exclusions-r304/historical','root-mathdb-cayley-review-intake-r363/DECISION']):
  bind(x['path'],x['sha256'],x['size'])
(D/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(D/'binding-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bound_paths':len(refs),'original_chunks':20,'frozen_inputs':8,'intake_exact_payload':True,'upstream_verifier_executed':False},indent=2)+'\n')
print('BIND PASS',len(refs))
