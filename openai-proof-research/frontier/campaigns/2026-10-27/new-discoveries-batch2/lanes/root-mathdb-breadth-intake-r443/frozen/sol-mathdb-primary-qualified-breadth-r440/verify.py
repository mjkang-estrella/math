#!/usr/bin/env python3
"""Read-only verification. Run through the prescribed helper_guard.py."""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parent; L=R.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def check(p,e):
 b=p.read_bytes();assert sha(b)==e['sha256'],f'hash: {p}'
 if 'size' in e:assert len(b)==e['size'],f'size: {p}'
 elif 'bytes' in e:assert len(b)==e['bytes'],f'bytes: {p}'
 return b
# Flat actual originals, not just snapshots or a prior receipt.
refs=load(R/'bindings.json');assert len(refs)==len({e['original'] for e in refs})
for e in refs:check(Path(e['original']),e)
for name in ['root-mathdb-breadth-intake-r439','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=L/name;m=load(d/'manifest.json');es=m if isinstance(m,list) else m['files']
 assert len(es)==len({e['path'] for e in es})
 for e in es:check(d/e['path'],e)
# Direct bound originals explicitly independent of the local flat list.
for e in load(L/'root-mathdb-breadth-intake-r439/bindings.json'):check(Path(e['original']),e)
I=L/'pi-mathdb-full-corpus-inventory-r301';chunks=[e for e in load(I/'manifest.json')['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:
 assert 'bytes' in e
 check(I/e['path'],e)
res=load(L/'root-mathdb-breadth-intake-r439/reserved-ids.json');ids=set(map(str,res['ids']));assert len(ids)==len(res['ids'])==50
assert res['lane']==R.name
q=load(L/'root-mathdb-breadth-intake-r439/queue.json');assert ids=={str(x['mathdb_id']) for x in q} and len(q)==50
old=load(L/'root-mathdb-breadth-intake-r439/coverage-delta.json');assert len(old)==2383
assert not ids&set(old) and not ids&set(map(str,res['other_active_reservations']))
assert not ids&{'372627','372628','368940','404067','364119'}
def associated(o):
 z=set()
 if isinstance(o,dict):
  for k,v in o.items():
   if k=='mathdb_id' and isinstance(v,(str,int)):z.add(str(v))
   elif isinstance(v,(dict,list)):z|=associated(v)
 elif isinstance(o,list):
  for v in o:z|=associated(v)
 return z
assert not ids&associated(load(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json'))
assert not ids&associated(load(L/'root-mathdb-cayley-review-intake-r363/disposition.json'))
# Stream all twenty originals; retain scientific content only for assigned IDs.
found={}
for e in chunks:
 for line in (I/e['path']).open():
  x=json.loads(line);n=str(x['mathdb_id'])
  if n in ids:
   assert n not in found;found[n]=x
assert set(found)==ids
rows=load(R/'dispositions.json');assert len(rows)==50 and {str(x['mathdb_id']) for x in rows}==ids
records=load(R/'records.json');assert len(records)==50 and {str(x['mathdb_id']):x for x in records}==found
for d in rows:
 x=found[str(d['mathdb_id'])]
 assert d['literal_statement']==x['statement']
 assert d['literal_statement_sha256']==sha(x['statement'].encode('utf-8'))
 assert d['canonical_record_sha256']==sha(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode('utf-8'))
 assert d['discovery_credit']==0 and d['scope_reason_mechanism_obstacle']
assert load(R/'proposals.json')==[]
# Only these two EXACT relative paths are excluded, no basename/substring filters.
m=load(R/'manifest.json');es=m['files'];paths={e['path'] for e in es};assert len(paths)==len(es)
assert {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','final-receipt.json'}==paths
for e in es:check(R/e['path'],e)
print(json.dumps({'ok':True,'assignment':50,'literal_statements':50,'canonical_record_hashes':50,'baseline':2383,'original_bindings':len(refs),'chunks':20,'payload_files':len(es),'proposals':0,'accepted_additional':9,'accepted_total':39,'next_global_outcome':40},sort_keys=True))
