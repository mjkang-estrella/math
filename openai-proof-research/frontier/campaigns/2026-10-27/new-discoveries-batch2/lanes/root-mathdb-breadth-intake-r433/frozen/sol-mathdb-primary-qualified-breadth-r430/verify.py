#!/usr/bin/env python3
"""Read-only verifier. Invoke under the assigned helper_guard, from any cwd."""
from pathlib import Path
import json,hashlib,sys
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r429';C=L/'pi-mathdb-full-corpus-inventory-r301'
def read(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e,key='size'):
 b=p.read_bytes();assert h(b)==e['sha256'],f'hash: {p}'
 if key in e:assert len(b)==e[key],f'size: {p}'
def canonical(d):return h(json.dumps(d,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode())
def main():
 bindings=read(O/'bindings.json');assert len({e['original'] for e in bindings})==len(bindings)
 for e in bindings:check(Path(e['original']),e)
 # Direct upstream manifest and original bindings only; never run upstream code or expand its bindings.
 for e in read(I/'manifest.json')['files']:check(I/e['path'],e)
 for e in read(I/'bindings.json'):check(Path(e['original']),e)
 chunks=[e for e in read(C/'manifest.json')['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
 for e in chunks:check(C/e['path'],e,'bytes')
 for lane,names in [('root-mathdb-accepted-exclusions-r304',{'accepted-exclusions.json','historical-dispositions.json'}),('root-mathdb-cayley-review-intake-r363',{'disposition.json','DECISION.md','reserved-ids.json'})]:
  m=read(L/lane/'manifest.json');entries=m if isinstance(m,list) else m['files'];es={e['path']:e for e in entries};assert names<=set(es)
  for name in names:check(L/lane/name,es[name])
 r=read(I/'reserved-ids.json');ids=r['ids'];assert len(ids)==len(set(ids))==50
 assert r['lane']==O.name and set(ids)=={x['mathdb_id'] for x in read(I/'queue.json')}
 other=r['other_active_reservations'];assert len(other)==len(set(other))==50
 assert not set(ids)&(set(other)|{372627,372628,368940,404067,364119})
 baseline=read(I/'coverage-delta.json');assert len(baseline)==2133 and not set(map(str,ids))&set(baseline)
 ds=read(O/'dispositions.json');assert len(ds)==50 and {x['mathdb_id'] for x in ds}==set(ids)
 cached={};origins={}
 for e in chunks:
  p=C/e['path']
  for no,line in enumerate(p.open(),1):
   d=json.loads(line)
   if d['mathdb_id'] in ids:
    assert d['mathdb_id'] not in cached
    cached[d['mathdb_id']]=d;origins[d['mathdb_id']]=(str(p),no)
 assert len(cached)==50
 for d in ds:
  original=cached[d['mathdb_id']];assert d['literal_statement']==original['statement']
  assert d['literal_statement_sha256']==h(original['statement'].encode())
  assert d['canonical_record_sha256']==canonical(original)
  assert (d['corpus_origin']['original'],d['corpus_origin']['line'])==origins[d['mathdb_id']]
  assert d['corpus_origin']['canonical_record_sha256']==canonical(original)
  assert d['credit']==0 and d['promoted'] is False and 'HOLD' in d['registry_evidence_level']
  for k in ['scope','mechanism_and_obstacle','primary_evidence_level','proof_evidence_level']:assert d[k]
 extracts=read(O/'assigned-records.json');assert len(extracts)==50
 assert {d['mathdb_id']:canonical(d) for d in extracts}=={i:canonical(d) for i,d in cached.items()}
 assert read(O/'proposals.json')==[]
 p=read(O/'provenance.json');assert p['counts']=={'additional':9,'total':39,'next':40}
 assert read(O/'registry-check.json')['mathdb_requests']==0
 for e in read(O/'sourcebytes.json'):
  if 'file' in e:check(O/e['file'],e,'bytes')
 for e in read(O/'excerpts.json'):
  lines=(O/e['file']).read_text().splitlines();assert e['text']=='\n'.join(lines[e['line_start']-1:e['line_end']])
 manifest=read(O/'manifest.json');excluded={'manifest.json','final-receipt.json'};assert set(manifest['excluded'])==excluded
 actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}-excluded
 listed={e['path'] for e in manifest['files']};assert len(listed)==len(manifest['files']) and actual==listed,(actual-listed,listed-actual)
 for e in manifest['files']:check(O/e['path'],e)
 return {'status':'PASS','lane':O.name,'original_bindings':len(bindings),'r301_original_chunks_verified':20,'exact_assignment':50,'disjoint_other_active':50,'baseline_reported_reviews':2133,'proposals':0,'payload_files':len(listed),'manifest_sha256':h((O/'manifest.json').read_bytes()),'limits':'Integrity and statement-screen verification only; no mathematical acceptance, novelty clearance, or complete proof-dependency audit.'}
try:print(json.dumps(main(),indent=2))
except Exception as e:
 print(json.dumps({'status':'FAIL','error':repr(e)},indent=2));sys.exit(1)
