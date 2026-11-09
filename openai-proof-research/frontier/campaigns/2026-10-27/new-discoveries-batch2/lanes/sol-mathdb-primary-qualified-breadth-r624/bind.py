from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r623'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p): return json.loads(p.read_text())
def digest(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
refs={}
def bind(p,h=None,n=None):
 x=digest(p)
 if h is not None: assert x['sha256']==h,(p,'hash')
 if n is not None: assert x['size']==n,(p,'size')
 refs[str(p)]=x
bind(I/'manifest.json','f92ea754d0c51662aea1b2372fbe76a7eeeb3e8521dc10106900651d3af82d89',10620)
m=j(I/'manifest.json'); assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
for x in m['files']: bind(I/x['path'],x['sha256'],x['size'])
bind(I/'verification-receipt.json')
for x in j(I/'bindings.json'):
 for k in ['original','copy']:bind(Path(x[k]),x['sha256'],x['bytes'])
rm=j(R/'manifest.json');chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for x in chunks+rm['frozen_inputs']:bind(R/x['path'],x['sha256'],x['bytes'])
for name in ['accepted-exclusions.json','historical-dispositions.json']:bind(L/'root-mathdb-accepted-exclusions-r304'/name)
for p in [L/'root-mathdb-cayley-review-intake-r363'/'DECISION.md',L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'sol-edge-irregulator-manuscript-packet-r1'/'packet/helper_guard.py']:bind(p)
q=j(I/'queue-r624.json');ids=j(I/'reserved-ids-r624.json');print('ids schema',type(ids));print('reservation',ids)
cov=set(map(int,j(I/'coverage-delta.json')));assert len(cov)==6533
sets=[]
for a in j(I/'active-breadth-reservations.json'):
 s=set(a['ids']);assert len(s)==50 and not(s&cov) and not(s&set(a['protected_ids']));sets.append(s)
assert not sets[0]&sets[1];assert {x['mathdb_id'] for x in q}==sets[1]
(D/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(D/'binding-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','files':len(refs),'chunks':20,'frozen_inputs':8,'baseline_literal_reviews':6533,'upstream_verifier_executed':False},indent=2)+'\n')
print('BOUND',len(refs))
