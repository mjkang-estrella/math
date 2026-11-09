#!/usr/bin/env python3
"""Read-only integrity verification. Run through the pinned helper_guard.py."""
from pathlib import Path
import json,hashlib,sys,datetime
W=Path(__file__).resolve().parent;L=W.parent
H=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def check(p,e):
 b=p.read_bytes();assert H(b)==e['sha256'],f'hash mismatch: {p}'
 n=e.get('size',e.get('bytes'))
 if n is not None:assert len(b)==n,f'size mismatch: {p}'
def entries(m):return m['files'] if isinstance(m,dict) else m
try:
 bindings=load(W/'bindings.json');assert len({x['original'] for x in bindings})==len(bindings)
 for e in bindings:
  p=Path(e['original']);assert p.is_absolute() and p.is_file();assert not p.is_symlink();check(p,e)
 bound={x['original'] for x in bindings}
 R=L/'root-mathdb-breadth-intake-r419';assert str(R/'manifest.json') in bound
 for e in entries(load(R/'manifest.json')):check(R/e['path'],e)
 for e in load(R/'bindings.json'):check(Path(e['original']),e)
 C=L/'pi-mathdb-full-corpus-inventory-r301';assert str(C/'manifest.json') in bound
 chunks=[e for e in entries(load(C/'manifest.json')) if e['path'].startswith('corpus/')]
 assert len(chunks)==20
 for e in chunks:
  assert 'bytes' in e;check(C/e['path'],e);assert str(C/e['path']) in bound
 for lane,files in [('root-mathdb-accepted-exclusions-r304',['accepted-exclusions.json','historical-dispositions.json','bindings.json']),('root-mathdb-cayley-review-intake-r363',['disposition.json','bindings.json'])]:
  base=L/lane;assert str(base/'manifest.json') in bound
  mm={e['path']:e for e in entries(load(base/'manifest.json'))}
  for f in files:check(base/f,mm[f]);assert str(base/f) in bound
 assert load(L/'root-mathdb-cayley-review-intake-r363/disposition.json')['mathdb_id']==364119
 res=load(R/'reserved-ids.json');ids=res['ids'];queue=load(R/'queue.json');baseline=load(R/'coverage-delta.json')
 assert res['lane']==W.name and len(ids)==len(set(ids))==50 and len(baseline)==1883
 assert set(ids)=={r['mathdb_id'] for r in queue} and len(queue)==50
 assert len(res['other_active_reservations'])==50
 assert not(set(ids)&set(res['other_active_reservations']))
 assert not(set(ids)&{int(i) for i in baseline})
 assert not(set(ids)&{372627,372628,368940,404067,364119})
 # Administrative exclusion identifiers, recursively recognized without treating arbitrary numbers as IDs.
 def exclusions(o):
  out=set()
  if isinstance(o,dict):
   for k,v in o.items():
    if k=='mathdb_id' and isinstance(v,int):out.add(v)
    elif k=='mathdb_ids' and isinstance(v,list):out.update(x for x in v if isinstance(x,int))
    out.update(exclusions(v))
  elif isinstance(o,list):
   for v in o:out.update(exclusions(v))
  return out
 for f in ['accepted-exclusions.json','historical-dispositions.json']:
  assert not(set(ids)&exclusions(load(L/'root-mathdb-accepted-exclusions-r304'/f)))
 originals={};loc={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line);i=r.get('mathdb_id')
   if i in ids:
    assert i not in originals;originals[i]=r;loc[i]={'original':str(p),'line':n}
 assert set(originals)==set(ids)
 cached=load(W/'records.json');assert len(cached)==50 and {r['mathdb_id'] for r in cached}==set(ids)
 for r in cached:assert r==originals[r['mathdb_id']]
 ds=load(W/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==set(ids)
 for d in ds:
  i=d['mathdb_id'];r=originals[i]
  assert d['literal_statement']==r['statement'] and d['statement_sha256']==H(r['statement'].encode())
  assert d['canonical_record_sha256']==H(json.dumps(r,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode())
  assert d['record_location']==loc[i] and d['accepted_credit']==0 and not d['new_full_proof_candidate']
  assert d['record_statement_review']=='full_literal_cached_statement_read'
  assert d['scope_and_quantifiers'] and d['concrete_mechanism_assessment'] and d['bounded_next_step_and_stop_reason']
  for e in d['source_evidence']:
   assert (W/e['bytes']).is_file() and (W/e['extraction']).is_file()
 assert load(W/'proposals.json')==[]
 for log in ['fetch-log.json','fetch2-log.json']:
  for e in load(W/'evidence'/log):
   if e.get('status')==200:check(W/'evidence'/(e['key']+'.body'),e)
 # Exact payload set; only these two literal relative paths are excluded.
 excluded={'manifest.json','final-verification-receipt.json'}
 actual={str(p.relative_to(W)) for p in W.rglob('*') if p.is_file() and str(p.relative_to(W)) not in excluded}
 mm=load(W/'manifest.json');listed={e['path'] for e in mm['files']}
 assert len(listed)==len(mm['files']) and actual==listed,{'missing':sorted(listed-actual),'extra':sorted(actual-listed)}
 for e in mm['files']:
  assert not (W/e['path']).is_symlink();check(W/e['path'],e)
 assert mm['excluded_exact_relative_paths']==sorted(excluded)
 assert load(W/'provenance.json')['counts_unchanged']=={'additional':9,'total':39,'next':40}
 print(json.dumps({'ok':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_originals_rechecked':len(bindings),'r419_manifest_and_bound_originals':True,'corpus_chunks_rechecked':20,'exact_assigned_dispositions':50,'baseline_reported_reviews':1883,'disjointness':True,'payload_files':len(listed),'payload_manifest_sha256':H((W/'manifest.json').read_bytes()),'proposals':0,'credit':0,'limits':'Integrity and provenance only; no mathematical acceptance or novelty clearance.'},indent=2))
except Exception as e:
 print(json.dumps({'ok':False,'error':str(e),'exception':type(e).__name__},indent=2));sys.exit(1)
