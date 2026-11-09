"""Independent read-only input/payload audit; writes only this lane's final receipt."""
from pathlib import Path
import hashlib,json,datetime,sys
L=Path(__file__).resolve().parent;B=L.parent
H=lambda b:hashlib.sha256(b).hexdigest()
J=lambda p:json.loads(Path(p).read_text())
def check(p,h,n=None):
 p=Path(p);assert p.is_file() and not p.is_symlink(),str(p)
 raw=p.read_bytes();assert H(raw)==h,'hash mismatch '+str(p)
 assert n is None or len(raw)==n,'size mismatch '+str(p)
 return raw
def exclusions(v):
 s=set()
 if isinstance(v,dict):
  for k,x in v.items():
   if k=='mathdb_id' and isinstance(x,int):s.add(x)
   elif k in ('mathdb_ids','problem_ids') and isinstance(x,list):s.update(i for i in x if isinstance(i,int))
   s.update(exclusions(x))
 elif isinstance(v,list):
  for x in v:s.update(exclusions(x))
 return s
try:
 manifest=J(L/'manifest.json');expected={e['path'] for e in manifest['files']}
 assert len(expected)==len(manifest['files'])
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}
 assert actual==expected|{'manifest.json','final-receipt.json'} or actual==expected|{'manifest.json'},'payload membership mismatch'
 for e in manifest['files']:check(L/e['path'],e['sha256'],e['bytes'])
 bindings=J(L/'bindings.json');assert len({e['path'] for e in bindings})==len(bindings)
 bound={e['path']:e for e in bindings}
 for e in bindings:check(e['path'],e['sha256'],e['bytes'])
 # Independently validate authoritative intake members and actual originals, without code execution.
 R=B/'root-mathdb-breadth-intake-r455'
 for name in ['root-mathdb-breadth-intake-r455','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
  root=B/name;assert str(root/'manifest.json') in bound
  m=J(root/'manifest.json');entries=m if isinstance(m,list) else m['files']
  for e in entries:
   p=root/e['path'];assert str(p) in bound
   check(p,e['sha256'],e.get('size',e.get('bytes')))
 for e in J(R/'bindings.json'):
  assert e['original'] in bound;check(e['original'],e['sha256'],e.get('size',e.get('bytes')))
 I=B/'pi-mathdb-full-corpus-inventory-r301';im=J(I/'manifest.json')
 chunks=[e for e in im['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
 assert {e['path'] for e in chunks}=={str(p.relative_to(I)) for p in (I/'corpus').glob('*.jsonl')}
 assert J(L/'inventory-frozen-membership.json')==im['frozen_inputs']
 for e in chunks+im['frozen_inputs']:
  assert str(I/e['path']) in bound;check(I/e['path'],e['sha256'],e['bytes'])
 a=J(R/'reserved-ids.json');ids=a['ids'];q=J(R/'queue.json');coverage=J(R/'coverage-delta.json')
 assert a['lane']==L.name and len(ids)==len(set(ids))==50
 assert ids==[x['mathdb_id'] for x in q] and len(coverage)==2783
 excluded=set(a['other_active_reservations'])|set(map(int,coverage))|{372627,372628,368940,404067,364119}
 for n in ['accepted-exclusions.json','historical-dispositions.json']:excluded|=exclusions(J(B/'root-mathdb-accepted-exclusions-r304'/n))
 excluded|=exclusions(J(B/'root-mathdb-cayley-review-intake-r363/disposition.json'))
 assert not set(ids)&excluded
 records=J(L/'records.json');ds=J(L/'dispositions.json');assert len(ds)==len(records)==50
 assert ids==[x['mathdb_id'] for x in ds]==[x['record']['mathdb_id'] for x in records]
 found={}
 for e in chunks:
  p=I/e['path']
  for line_no,line in enumerate(p.open(),1):
   r=json.loads(line);i=r['mathdb_id']
   if i in ids:
    assert i not in found;found[i]=(r,str(p),line_no)
 assert set(found)==set(ids)
 for x,d in zip(records,ds):
  r,p,line=found[d['mathdb_id']]
  assert r==x['record']
  assert x['original_chunk']==d['original_chunk']==p and x['original_line']==d['original_line']==line
  assert r['statement']==d['literal_statement']==d['full_scope']
  assert H(r['statement'].encode('utf-8'))==d['statement_sha256']==x['statement_sha256']
  assert H(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())==d['canonical_record_sha256']==x['canonical_record_sha256']
  assert d['full_literal_statement_read'] and d['quantifiers_reviewed']
  assert d['accepted_credit']==0 and not d['proposal']
  assert all(k in d for k in ['technical_disposition','source_level','proof_level','registry_level','bounded_check_status','strongest_objection','formal_dependencies','certificate_size','prior_gaps'])
 assert J(L/'proposals.json')==[]
 notes=(L/'technical-notes.tsv').read_text().splitlines();assert len(notes)==50
 assert {int(x.split('\t')[0]) for x in notes}==set(ids)
 for e in J(L/'source-provenance.json'):
  if 'file' in e:
   check(L/e['file'],e['sha256'],e['bytes']);assert e['url'].startswith('https://') and e['utc'] and e['version']
   if 'text_file' in e:check(L/e['text_file'],e['text_sha256'])
 counts=J(L/'review-counts.json');assert counts['additional']==9 and counts['total']==39 and counts['next']==40 and counts['new_credit']==0
 receipt=dict(integrity='PASS',mathematical_pass=False,novelty_pass=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=H((L/'manifest.json').read_bytes()),payload_files=len(expected),flat_bindings=len(bindings),chunks_verified_in_place=20,assignment=50,dispositions=50,proposals=0,reported_baseline=2783,new_credit=0,counts_unchanged=dict(additional=9,total=39,next=40),upstream_code_executed=False,root_acceptance_required=True)
 (L/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
except Exception as error:
 print('INTEGRITY FAIL: '+repr(error),file=sys.stderr);sys.exit(1)
