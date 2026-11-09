from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent; L=D.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r699'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def h(p):
 b=p.read_bytes(); return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 x=h(p); assert x['sha256']==e['sha256'] and x['size']==e.get('size',e.get('bytes')),(p,x); return x
bindings=[h(I/'manifest.json'),h(I/'verification-receipt.json')]
m=json.loads((I/'manifest.json').read_text()); expected={x['path'] for x in m['files']}; actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']); assert expected==actual
for e in m['files']: bindings.append(check(I/e['path'],e))
for e in json.loads((I/'bindings.json').read_text()):
 for k in ['original','copy']: bindings.append(check(Path(e[k]),e))
cm=json.loads((C/'manifest.json').read_text()); chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]; assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']: bindings.append(check(C/e['path'],e))
paths=[B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363'/'DECISION.md',B.parents[3]/'sources'/'upstream.json']
for p in paths:
 if p.exists(): bindings.append(h(p))
# Bound exact content before any later scientific/context reading.
(D/'initial-bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bindings':bindings,'checks':{'intake_exact_payload':True,'direct_pairs':len(json.loads((I/'bindings.json').read_text())),'chunks':20,'frozen_inputs':8}},indent=2)+'\n')
print('PASS intake exact payload, all direct original/copy pairs, 20 chunks, 8 frozen inputs; bound',len(bindings),'references')
print('reservation keys',json.loads((I/'reserved-ids-r700.json').read_text()).keys())
print('active sets',[(e.get('lane'),len(e.get('ids',[])),e.get('status')) for e in json.loads((I/'active-breadth-reservations.json').read_text())])
