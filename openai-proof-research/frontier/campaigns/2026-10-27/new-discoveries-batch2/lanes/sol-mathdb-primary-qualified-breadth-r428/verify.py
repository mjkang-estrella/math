#!/usr/bin/env python3
"""Read-only independent verification. Run only through the fixed helper_guard.py."""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parent;L=R.parent
EXCLUDED={'manifest.json','final-receipt.json'}
def load(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,h,s=None):
 b=p.read_bytes();assert sha(b)==h,('hash',str(p));assert s is None or len(b)==s,('size',str(p))
def entries(p):
 m=load(p);return m['files'] if isinstance(m,dict) else m
def check_manifest(d):
 for e in entries(d/'manifest.json'):check(d/e['path'],e['sha256'],e.get('size',e.get('bytes')))
# Actual original paths, not copied certificates or upstream verifier receipts.
refs=load(R/'bindings.json');assert len({e['original'] for e in refs})==len(refs)
for e in refs:check(Path(e['original']),e['sha256'],e['size'])
A=L/'root-mathdb-breadth-intake-r427';check_manifest(A)
for e in load(A/'bindings.json'):check(Path(e['original']),e['sha256'],e['size'])
I=L/'pi-mathdb-full-corpus-inventory-r301'
chunks=[e for e in entries(I/'manifest.json') if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:check(I/e['path'],e['sha256'],e['bytes'])
for n in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:check_manifest(L/n)
reservation=load(A/'reserved-ids.json');ids=set(reservation['ids']);assert len(ids)==50
assert ids=={o['mathdb_id'] for o in load(A/'queue.json')}
other=set(reservation['other_active_reservations']);assert len(other)==50
baseline=load(A/'coverage-delta.json');assert len(baseline)==2083
assert not ids.intersection(map(int,baseline));assert not ids&other
assert not ids&{372627,372628,368940,404067,364119}
# Independently stream actual original corpus; compare full retained records and literal statements.
originals={};locations={}
for e in chunks:
 p=I/e['path']
 for lineno,line in enumerate(p.open(),1):
  o=json.loads(line)
  if o['mathdb_id'] in ids:
   i=o['mathdb_id'];assert i not in originals;originals[i]=o;locations[i]={'mathdb_id':i,'original':str(p),'line':lineno}
assert set(originals)==ids
retained=load(R/'records.json');assert len(retained)==50
assert {o['mathdb_id']:o for o in retained}==originals
rows=load(R/'dispositions.json');assert len(rows)==50 and {o['mathdb_id'] for o in rows}==ids
for d in rows:
 o=originals[d['mathdb_id']]
 assert d['literal_statement']==o['statement']
 assert d['statement_sha256']==sha(o['statement'].encode('utf8'))
 assert d['canonical_record_sha256']==sha(json.dumps(o,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode('utf8'))
 assert d['record_location']==locations[d['mathdb_id']]
 assert d['scope'] and d['reason_and_obstacle'] and d['levels']['primary'] and d['levels']['proof'] and d['levels']['registry']
 assert d['credit']==0
for e in load(R/'source-excerpts.json')+load(R/'extra-excerpts.json'):
 assert e['excerpt']==(R/e['file']).read_text().split('\f')[e['physical_page']-1]
assert load(R/'proposals.json')==[]
assert load(R/'provenance.json')['counts_unchanged']=={'additional':9,'total':39,'next':40}
files=entries(R/'manifest.json');paths=[e['path'] for e in files];assert len(paths)==len(set(paths))
actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-EXCLUDED
assert actual==set(paths),('payload_set_mismatch',sorted(actual-set(paths)),sorted(set(paths)-actual))
for e in files:check(R/e['path'],e['sha256'],e['size'])
print(json.dumps({'status':'PASS','original_bindings':len(refs),'original_chunks':20,'assignment':50,'baseline':2083,'disjoint':True,'literal_and_canonical_hashes':50,'exact_payload_files':len(files),'proposals':0}))
