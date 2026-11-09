from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;L=D.parent;R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def dump(n,x):(D/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
refs={}
def bind(p,e=None):
 b=p.read_bytes();x={'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if e:assert x['size']==e.get('size',e.get('bytes')) and x['sha256']==e['sha256'],str(p)
 refs[str(p)]=x;return x
for n in [585,587]:
 I=L/f'root-mathdb-breadth-intake-r{n}';bind(I/'manifest.json');m=load(I/'manifest.json');expected={x['path'] for x in m['files']};assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==expected
 for x in m['files']:bind(I/x['path'],x)
 bind(I/'verification-receipt.json')
 for x in load(I/'bindings.json'):
  bind(Path(x['original']),x);bind(Path(x['copy']),x);assert Path(x['original']).read_bytes()==Path(x['copy']).read_bytes()
inv=load(R/'manifest.json');chunks=[x for x in inv['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
for x in chunks+inv['frozen_inputs']:bind(R/x['path'],x)
for p in [L/'root-mathdb-accepted-exclusions-r304'/n for n in ['accepted-exclusions.json','historical-dispositions.json']]+[L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'sol-mathdb-primary-qualified-breadth-r542/failures.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 bind(p)
for lane in ['sol-mathdb-primary-qualified-breadth-r578','sol-mathdb-primary-qualified-breadth-r584']:
 for p in (L/lane).glob('*'):
  if p.is_file() and ('failure' in p.name or p.name in ['flat-bindings.json','source-provenance.json','source-coverage.json']):bind(p)
dump('flat-bindings.json',list(refs.values()));dump('binding-receipt.json',{'integrity':'PASS','corpus_chunks':20,'frozen_inputs':8,'r585_and_r587_exact_payload_and_direct_pairs':True,'scientific_content_read_before_receipt':False});print('BOUND',len(refs))
for n in [585,587]:
 I=L/f'root-mathdb-breadth-intake-r{n}';print(n,'coverage',list(load(I/'coverage-delta.json')),'active',str(load(I/'active-breadth-reservations.json'))[-1800:])
print('frozen inputs',inv['frozen_inputs'])
