from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r705';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
refs={}
def bind(p,e=None):
 b=p.read_bytes();a={'path':str(p),'sha256':h(b),'size':len(b)}
 if e:assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),str(p)
 refs[str(p)]=a
 return a
def exact(root,m):
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
 for e in m['files']:bind(root/e['path'],e)
bind(I/'manifest.json');bind(I/'verification-receipt.json');exact(I,j(I/'manifest.json'))
for e in j(I/'bindings.json'):
 for k in ['original','copy']:bind(Path(e[k]),e)
cm=j(C/'manifest.json');bind(C/'manifest.json',next(e for e in j(I/'bindings.json') if e['original']==str(C/'manifest.json')))
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
# Direct flat references only; no historical tree expansion.
for e in j(L/'sol-mathdb-primary-qualified-breadth-r702/flat-bindings.json'):bind(Path(e['path']),e)
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/upstream.json'),Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md')]:bind(p)
cov=j(I/'coverage-delta.json');assert len(cov)==8533
active=j(I/'active-breadth-reservations.json');seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
assert len(seen)==150 and len(active)==3
for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
q=j(I/'queue-r706.json');res=j(I/'reserved-ids-r706.json');assert len(q)==50 and {r['mathdb_id'] for r in q}==set(res['ids'])
assert next(r for r in active if r['lane']==P.name)['ids']==res['ids']
assert any(r['lane'].endswith('r628') and r['status']=='rate_limit_held_not_reconciled' for r in active)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'initial-checks.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'PASS':True,'original_chunks':20,'frozen_inputs':8,'baseline':8533,'reserved_sets':3,'reserved_ids':150,'exact_intake':True,'direct_pairs':len(j(I/'bindings.json')),'before_scientific_reading':True},indent=2)+'\n')
print('PASS: prereading bindings, exact intake, direct pairs, 20 chunks, 8 inputs, and three disjoint reservations.')
