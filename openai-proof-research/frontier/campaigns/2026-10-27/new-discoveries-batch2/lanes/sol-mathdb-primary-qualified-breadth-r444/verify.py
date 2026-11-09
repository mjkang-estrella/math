#!/usr/bin/env python3
"""Read-only upstream verification; only writes this lane's excluded final receipt."""
from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent;L=R.parent
EXCLUDED={'manifest.json','final-receipt.json'}
def j(p):return json.loads(p.read_text())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s):
 assert p.is_file(),str(p)
 assert p.stat().st_size==s,(str(p),'size mismatch')
 assert digest(p)==h,(str(p),'hash mismatch')
refs=j(R/'bindings.json');assert len(refs)==len({e['original'] for e in refs})
refmap={e['original']:e for e in refs}
for e in refs:check(Path(e['original']),e['sha256'],e['size'])
# Independently check the complete bound manifests, including r301's bytes field.
for name in ['root-mathdb-breadth-intake-r443','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 p=L/name;m=p/'manifest.json';assert str(m) in refmap
 obj=j(m);entries=obj['files'] if isinstance(obj,dict) else obj
 assert len(entries)==len({e['path'] for e in entries})
 for e in entries:
  q=p/e['path'];bound=refmap[str(q)]
  assert bound['sha256']==e['sha256']
  s=e.get('size',e.get('bytes',bound['size']));check(q,e['sha256'],s)
# Direct r443 originals are checked without following their binding graphs.
for e in j(L/'root-mathdb-breadth-intake-r443/bindings.json'):
 q=Path(e['original']);assert str(q) in refmap;check(q,e['sha256'],e['size'])
I=L/'pi-mathdb-full-corpus-inventory-r301'
chunks=[e for e in j(I/'manifest.json')['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:check(I/e['path'],e['sha256'],e['bytes'])
a=j(L/'root-mathdb-breadth-intake-r443/reserved-ids.json');ids=set(a['ids'])
assert len(a['ids'])==len(ids)==50 and a['lane']==R.name
assert not ids&set(a['other_active_reservations']) and len(set(a['other_active_reservations']))==50
baseline=j(L/'root-mathdb-breadth-intake-r443/coverage-delta.json');assert len(baseline)==2483
assert not set(map(str,ids))&set(baseline)
assert not ids&{372627,372628,368940,404067,364119}
assert ids=={x['mathdb_id'] for x in j(L/'root-mathdb-breadth-intake-r443/queue.json')}
found={};locations={}
for e in chunks:
 for line_number,line in enumerate((I/e['path']).open(),1):
  x=json.loads(line);n=x['mathdb_id']
  if n in ids:
   assert n not in found;found[n]=x;locations[n]=(str(I/e['path']),line_number)
assert set(found)==ids
rows=j(R/'dispositions.json');assert len(rows)==50 and {x['mathdb_id'] for x in rows}==ids
for row in rows:
 x=found[row['mathdb_id']];st=x['statement']
 assert row['literal_statement']==st and row['record_statement_level']=='full_literal_read'
 assert row['literal_statement_sha256']==hashlib.sha256(st.encode()).hexdigest()
 assert row['canonical_record_sha256']==hashlib.sha256(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()
 assert row['discovery_credit']==0 and row['prior_clearance'] is False
 assert row['registry_level']=='HOLD_current_registry_not_checked'
assert j(R/'records.json')==sorted(found.values(),key=lambda x:x['mathdb_id'])
for e in j(R/'record-locations.json'):assert (e['path'],e['line'])==locations[e['id']]
assert j(R/'proposals.json')==[]
for e in j(R/'source-excerpts.json'):
 a,b=e['lines_inclusive'];assert e['mathdb_id'] in ids
 assert '\n'.join((R/e['text_path']).read_text().split('\n')[a-1:b])==e['excerpt']
for n in ['source-provenance.json','pdf-provenance.json']:
 for e in j(R/n):
  if 'file' in e:check(R/e['file'],e['sha256'],e['size'])
checkdata=j(R/'bounded-check.json')
assert checkdata['residue_solutions']==[[a,b] for a in range(4) for b in range(4) if (a+b)%4==0 and (a*a+b*b)%4==0]
files=j(R/'manifest.json')['files'];expected={e['path'] for e in files}
actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-EXCLUDED
assert len(files)==len(expected) and actual==expected,{'extra':sorted(actual-expected),'missing':sorted(expected-actual)}
for e in files:check(R/e['path'],e['sha256'],e['size'])
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':digest(R/'manifest.json'),'original_bindings_checked':len(refs),'corpus_chunks_checked':20,'assigned_literal_statements_checked':50,'baseline_distinct_reported_reviews':2483,'primary_relevant_sections_reported':9,'external_concluding_proof_sections_reported':1,'proof_dependency_closure_audited':False,'proposals':0,'registry_clearance':False,'counts_unchanged':{'additional':9,'total':39,'next':40},'payload_files':len(files),'scientific_limit':'integrity and assignment verification, not independent proof replay'}
(R/'final-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
print(json.dumps(receipt,sort_keys=True))
