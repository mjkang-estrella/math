#!/usr/bin/env python3
"""Read-only verification except optional own final receipt. Run under helper_guard.py."""
from pathlib import Path
import json,hashlib,sys
O=Path(__file__).resolve().parent; L=O.parent
J=lambda p:json.loads(Path(p).read_text())
H=lambda b:hashlib.sha256(b).hexdigest()
def check(p,r):
 b=Path(p).read_bytes()
 assert H(b)==r['sha256'],f'hash mismatch: {p}'
 size=r.get('size',r.get('bytes'))
 if size is not None:assert len(b)==size,f'size mismatch: {p}'
 return b
bindings=J(O/'bindings.json'); bound={r['original']:r for r in bindings}
assert len(bound)==len(bindings)
for r in bindings:
 assert Path(r['original']).is_absolute() and 'size' in r
 check(r['original'],r)
def upstream_manifest(name):
 p=L/name/'manifest.json';assert str(p) in bound
 m=J(p); entries=m if isinstance(m,list) else m['files']
 assert len({x['path'] for x in entries})==len(entries)
 for e in entries:
  original=p.parent/e['path'];assert str(original) in bound
  check(original,e)
 return entries
upstream_manifest('root-mathdb-breadth-intake-r423')
for r in J(L/'root-mathdb-breadth-intake-r423/bindings.json'):
 assert r['original'] in bound
 check(r['original'],r)
m=upstream_manifest('pi-mathdb-full-corpus-inventory-r301')
chunks=[r for r in m if r['path'].startswith('corpus/')]
assert len(chunks)==20
assert all('bytes' in r for r in chunks)
upstream_manifest('root-mathdb-accepted-exclusions-r304');upstream_manifest('root-mathdb-cayley-review-intake-r363')
acc=J(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json');J(L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json')
assert acc['accepted_family_count']==39
assert J(L/'root-mathdb-cayley-review-intake-r363/disposition.json')['mathdb_id']==364119
r=J(L/'root-mathdb-breadth-intake-r423/reserved-ids.json');q=J(L/'root-mathdb-breadth-intake-r423/queue.json');baseline=J(L/'root-mathdb-breadth-intake-r423/coverage-delta.json')
ids=r['ids'];assert len(ids)==len(set(ids))==50 and r['lane']==O.name
assert len(q)==50 and set(ids)=={x['mathdb_id'] for x in q}
assert len(baseline)==1983 and len(r['other_active_reservations'])==50
assert not set(ids)&(set(map(int,baseline))|set(r['other_active_reservations'])|{372627,372628,368940,404067,364119})
actual={};locations={}
for e in chunks:
 p=L/'pi-mathdb-full-corpus-inventory-r301'/e['path']
 for n,line in enumerate(p.open(),1):
  v=json.loads(line)
  if v['mathdb_id'] in ids:
   i=v['mathdb_id'];assert i not in actual
   actual[i]=v;locations[i]=(str(p),n)
assert set(actual)==set(ids)
stored=J(O/'records.json');assert len(stored)==50
assert {x['mathdb_id']:x for x in stored}==actual
loc=J(O/'record-locations.json');assert len(loc)==50
byloc={x['mathdb_id']:x for x in loc};assert len(byloc)==50
D=J(O/'dispositions.json');assert len(D)==50 and {x['mathdb_id'] for x in D}==set(ids)
for d in D:
 i=d['mathdb_id'];a=actual[i];p,n=locations[i]
 canonical=H(json.dumps(a,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode('utf8'))
 statement=H(a['statement'].encode('utf8'))
 assert d['literal_statement']==a['statement'] and d['uuid']==a['uuid'] and d['canonical_url']==a['canonical_url']
 assert d['canonical_record_sha256']==canonical==byloc[i]['canonical_sha256']
 assert d['statement_sha256']==statement==byloc[i]['statement_sha256']
 assert byloc[i]['original']==p and byloc[i]['line']==n and d['record_location']==byloc[i]
 assert d['scope_and_reason'] and d['evidence_levels']['registry']
 assert d['accepted_credit']==0 and not d['brief_qualified']
assert J(O/'proposals.json')==[]
assert J(O/'provenance.json')['counts_unchanged']=={'additional':9,'total':39,'next':40}
for name in ['source-provenance.json','independent-successor-provenance.json']:
 for x in J(O/name):
  assert x['status']==200
  check(O/x['path'],x)
for x in J(O/'source-excerpts.json'):
 lines=(O/x['source']).read_text().splitlines()
 assert x['text']=='\n'.join(lines[x['first_line']-1:x['last_line']])
manifest=J(O/'manifest.json'); excluded={'manifest.json','final-receipt.json'}
assert manifest['excluded_exact_relative_paths']==sorted(excluded)
entries=manifest['files'];expected={e['path'] for e in entries}
assert len(expected)==len(entries)
found={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}-excluded
assert found==expected,{'extra':sorted(found-expected),'missing':sorted(expected-found)}
for p in O.rglob('*'):assert not p.is_symlink(),f'symlink: {p}'
for e in entries:
 assert e['path'] not in excluded
 check(O/e['path'],e)
receipt={'status':'PASS','assigned':50,'literal_and_canonical_records_checked':50,'corpus_chunks_verified':20,'actual_original_bindings_verified':len(bindings),'baseline':1983,'qualified_briefs':0,'mathdb_requests':0,'payload_files':len(entries),'manifest_sha256':H((O/'manifest.json').read_bytes()),'counts_unchanged':{'additional':9,'total':39,'next':40},'limitations':'Integrity and assignment verification only; not independent theorem/proof verification.'}
if '--receipt' in sys.argv:(O/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
