#!/usr/bin/env python3
"""Run through the assigned helper_guard; read-only, exits nonzero on mismatch."""
from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent;L=O.parent
J=lambda p:json.loads(p.read_text())
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def check(p,e):
 assert p.is_file(),('missing',str(p))
 assert digest(p)==e['sha256'],('sha256',str(p))
 size=e.get('size',e.get('bytes'))
 if size is not None:assert p.stat().st_size==size,('bytes',str(p))
def canon(x):return hashlib.sha256(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode('utf8')).hexdigest()
# Exact relative exclusions only: a nested manifest/receipt would be payload.
excluded={'manifest.json','final-receipt.json'}
m=J(O/'manifest.json')['files'];names=[e['path'] for e in m]
assert len(names)==len(set(names))
actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}-excluded
assert set(names)==actual,('payload_set',sorted(set(names)^actual))
for e in m:
 rel=Path(e['path']);assert not rel.is_absolute() and '..' not in rel.parts
 check(O/rel,e)
bindings=J(O/'bindings.json');bound={e['path']:e for e in bindings}
assert len(bound)==len(bindings)
for e in bindings:check(Path(e['path']),e)
# Independently interpret original manifests, never execute their verifiers.
for name in ['root-mathdb-breadth-intake-r433','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=L/name;mp=d/'manifest.json';assert str(mp) in bound
 src=J(mp);entries=src if isinstance(src,list) else src['files']
 for e in entries:
  p=d/e['path'];assert str(p) in bound;check(p,e)
 if name=='pi-mathdb-full-corpus-inventory-r301':
  chunks=[e for e in entries if e['path'].startswith('corpus/mathdb-normalized-chunk-')]
  assert {e['path'] for e in chunks}=={f'corpus/mathdb-normalized-chunk-{i:04d}.jsonl' for i in range(1,21)}
  assert all('bytes' in e for e in chunks)
for e in J(L/'root-mathdb-breadth-intake-r433/bindings.json'):
 p=Path(e['original']);assert str(p) in bound;check(p,e)
a=J(L/'root-mathdb-breadth-intake-r433/reserved-ids.json');ids=a['ids'];wanted=set(ids)
assert len(ids)==len(wanted)==50
q=J(L/'root-mathdb-breadth-intake-r433/queue.json');assert {x['mathdb_id'] for x in q}==wanted and len(q)==50
base=J(L/'root-mathdb-breadth-intake-r433/coverage-delta.json');assert len(base)==2233
assert not wanted&set(map(int,base))
assert len(a['other_active_reservations'])==50 and not wanted&set(a['other_active_reservations'])
assert not wanted&{372627,372628,368940,404067,364119}
records={}
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line);i=r['mathdb_id']
  if i in wanted:
   assert i not in records;records[i]=(r,str(p),n)
assert set(records)==wanted
saved=J(O/'assigned-records.json');assert len(saved)==50 and {x['record']['mathdb_id'] for x in saved}==wanted
for x in saved:
 r,p,n=records[x['record']['mathdb_id']];assert x['record']==r and x['original']==p and x['line']==n
 assert x['literal_statement_sha256']==hashlib.sha256(r['statement'].encode()).hexdigest()
 assert x['canonical_record_sha256']==canon(r)
d=J(O/'dispositions.json');assert len(d)==50 and {x['mathdb_id'] for x in d}==wanted
for x in d:
 r,p,n=records[x['mathdb_id']]
 assert x['literal_statement']==r['statement']
 assert x['literal_statement_sha256']==hashlib.sha256(r['statement'].encode()).hexdigest()
 assert x['canonical_statement_sha256']==canon(r['statement']) and x['canonical_record_sha256']==canon(r)
 assert (x['original_chunk'],x['original_line'])==(p,n)
 assert x['scope_quantifiers'] and x['reason_and_mechanism'] and x['registry_level']
 assert x['accepted_credit']==0 and x['prior_cleared'] is False
assert J(O/'proposals.json')==[]
assert J(O/'administrative-check.json')['counts']=={'additional':9,'total':39,'next':40}
for e in J(O/'sourcebytes.json'):check(O/e['path'],e)
print(json.dumps({'status':'PASS','assigned_dispositions':50,'baseline_reported':2233,'original_chunks_checked':20,'bound_originals':len(bindings),'payload_files':len(m),'proposals':0,'counts_unchanged':[9,39,40]}))
