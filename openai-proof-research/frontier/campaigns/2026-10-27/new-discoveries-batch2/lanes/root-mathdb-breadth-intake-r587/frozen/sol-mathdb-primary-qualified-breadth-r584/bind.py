from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r583'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def digest(p):
 b=p.read_bytes(); return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def load(p):return json.loads(p.read_text())
def dump(n,x):(D/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
refs={}
def bind(p,e=None):
 x=digest(p)
 if e:assert x['size']==e.get('size',e.get('bytes')) and x['sha256']==e['sha256'],str(p)
 refs[str(p)]=x
 return x
assert bind(I/'manifest.json')['sha256']=='bb48ce18c88c4dd882abfab1a66d83404fd238840ad71055b9f1d44f9cadd359'
m=load(I/'manifest.json'); expected={x['path'] for x in m['files']}; actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']); assert actual==expected
for x in m['files']:bind(I/x['path'],x)
bind(I/'verification-receipt.json')
for x in load(I/'bindings.json'):
 bind(Path(x['original']),x);bind(Path(x['copy']),x);assert Path(x['original']).read_bytes()==Path(x['copy']).read_bytes()
inv=load(R/'manifest.json');chunks=[x for x in inv['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
for x in chunks+inv['frozen_inputs']:bind(R/x['path'],x)
for p in [L/'root-mathdb-accepted-exclusions-r304'/n for n in ['accepted-exclusions.json','historical-dispositions.json']]+[L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'sol-mathdb-primary-qualified-breadth-r542/failures.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 bind(p)
dump('flat-bindings.json',list(refs.values()))
dump('binding-receipt.json',{'integrity':'PASS','intake_exact_payload':len(expected),'original_copy_pairs':len(load(I/'bindings.json')),'original_corpus_chunks':20,'frozen_inputs':8,'scientific_content_read_before_this_receipt':False})
print('BOUND',len(refs));print('reservation',load(I/'reserved-ids.json')); print('active',load(I/'active-breadth-reservations.json').keys());print('coverage keys',load(I/'coverage-delta.json').keys())
