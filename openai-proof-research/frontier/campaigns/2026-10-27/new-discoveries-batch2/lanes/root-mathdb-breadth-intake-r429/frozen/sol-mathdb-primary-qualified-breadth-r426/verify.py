#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;L=R.parent
EXCLUDED={'manifest.json','final-receipt.json'}
def load(p):return json.loads(p.read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def check(p,e):
 assert p.is_file(),str(p)
 assert sha(p)==e['sha256'],str(p)+' hash'
 if 'size' in e:assert p.stat().st_size==e['size'],str(p)+' size'
 if 'bytes' in e:assert p.stat().st_size==e['bytes'],str(p)+' bytes'
def canon(x):return json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode('utf-8')
bindings=load(R/'bindings.json');bound={x['original']:x for x in bindings};assert len(bound)==len(bindings)
for e in bindings:check(Path(e['original']),e)
for name in ['root-mathdb-breadth-intake-r425','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=L/name;m=load(d/'manifest.json');entries=m['files'] if isinstance(m,dict) else m
 assert str(d/'manifest.json') in bound
 for e in entries:check(d/e['path'],e);assert str(d/e['path']) in bound
A=L/'root-mathdb-breadth-intake-r425'
for e in load(A/'bindings.json'):
 check(Path(e['original']),e);assert e['original'] in bound
I=L/'pi-mathdb-full-corpus-inventory-r301';assert str(I/'manifest.json') in bound
chunks=[e for e in load(I/'manifest.json')['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:assert 'bytes' in e;check(I/e['path'],e);assert str(I/e['path']) in bound
assignment=load(A/'reserved-ids.json');ids=list(map(str,assignment['ids']));queue=load(A/'queue.json');base=load(A/'coverage-delta.json')
assert len(ids)==len(set(ids))==50 and set(ids)=={str(x['mathdb_id']) for x in queue} and len(queue)==50
assert len(base)==2033 and len(set(map(str,assignment['other_active_reservations'])))==50
assert not set(ids)&(set(base)|set(map(str,assignment['other_active_reservations']))|{'372627','372628','368940','404067','364119'})
found={}
for e in chunks:
 for line in (I/e['path']).open():
  x=json.loads(line);n=str(x['mathdb_id'])
  if n in ids:assert n not in found;found[n]=x
assert set(found)==set(ids)
records=load(R/'selected-records.json');rows=load(R/'dispositions.json')
assert len(records)==len(rows)==50 and [str(x['mathdb_id']) for x in rows]==ids
assert {str(x['mathdb_id']):x for x in records}==found
for row in rows:
 x=found[str(row['mathdb_id'])];assert row['literal_statement']==x['statement']
 assert hashlib.sha256(x['statement'].encode()).hexdigest()==row['statement_sha256']
 assert hashlib.sha256(canon(x)).hexdigest()==row['canonical_record_sha256']
 assert row['scope'] and row['reason'] and row['credit']==0 and row['prior_cleared'] is False
 assert row['evidence_levels']['literal_cached_statement_read'] is True
assert load(R/'proposals.json')==[]
for e in load(R/'sourcebytes.json'):check(R/e['path'],e)
for e in load(R/'source-provenance.json'):
 if 'path' in e:check(R/e['path'],e)
for e in load(R/'excerpts.json'):
 lines=(R/e['file']).read_text().splitlines();assert e['text']=='\n'.join(lines[e['first_line']-1:e['last_line']])
from fractions import Fraction
assert 1-Fraction(3,2)*Fraction(1,2)==Fraction(1,4)
assert load(R/'calculation.json')['noise_ratio_exponent']=='1/4'
assert load(R/'provenance.json')['counts']=={'additional':9,'total':39,'next':40}
entries=load(R/'manifest.json')['files'];paths={e['path'] for e in entries}
assert len(paths)==len(entries)
actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-EXCLUDED
assert actual==paths,{'extra':sorted(actual-paths),'missing':sorted(paths-actual)}
for e in entries:check(R/e['path'],e)
receipt={'status':'PASS','assignment_records':50,'baseline_records':2033,'original_chunks_verified':20,'original_bindings_verified':len(bindings),'payload_files':len(entries),'manifest_sha256':sha(R/'manifest.json'),'counts_unchanged':{'additional':9,'total':39,'next':40},'timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'integrity and exact assignment verification; not scientific proof or novelty certification'}
(R/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
