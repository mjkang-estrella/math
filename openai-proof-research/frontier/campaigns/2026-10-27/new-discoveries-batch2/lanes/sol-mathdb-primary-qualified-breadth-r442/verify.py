#!/usr/bin/env python3
"""Run through the assigned helper_guard.py; --seal creates only this lane's manifest."""
from pathlib import Path
import json,hashlib,sys,datetime
R=Path(__file__).resolve().parent;L=R.parent
EXCLUDE={'manifest.json','final-receipt.json'}
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def check(p,h,s=None):
 assert p.is_file(),str(p)
 assert s is None or p.stat().st_size==s,('size',str(p))
 assert digest(p)==h,('sha256',str(p))
def read(p):return json.loads(p.read_text())
def payload(d):return {str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}
def upstream(d):
 m=read(d/'manifest.json');es=m['files']+m.get('frozen_inputs',[]) if isinstance(m,dict) else m
 assert payload(d)-{'manifest.json','verification-receipt.json'}=={e['path'] for e in es},('upstream payload',str(d))
 for e in es:check(d/e['path'],e['sha256'],e.get('size',e.get('bytes')))
 return es
try:
 refs=read(R/'bindings.json');assert len({e['path'] for e in refs})==len(refs)
 for e in refs:check(Path(e['path']),e['sha256'],e['size'])
 A=L/'root-mathdb-breadth-intake-r441';I=L/'pi-mathdb-full-corpus-inventory-r301'
 for d in [A,I,L/'root-mathdb-accepted-exclusions-r304',L/'root-mathdb-cayley-review-intake-r363']:upstream(d)
 bound={e['path']:e for e in refs}
 for e in read(A/'bindings.json'):
  p=Path(e['original']);check(p,e['sha256'],e['size']);assert str(p) in bound
 chunks=[e for e in read(I/'manifest.json')['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
 for e in chunks:
  assert 'bytes' in e;check(I/e['path'],e['sha256'],e['bytes']);assert str(I/e['path']) in bound
 a=read(A/'reserved-ids.json');ids=list(map(str,a['ids']));assert len(ids)==len(set(ids))==50
 assert a['lane']==R.name
 queue=read(A/'queue.json');assert [str(x['mathdb_id']) for x in queue]==ids
 baseline=read(A/'coverage-delta.json');assert len(baseline)==2433
 active=set(map(str,a['other_active_reservations']));assert len(active)==50
 assert not set(ids)&(set(baseline)|active|{'372627','372628','368940','404067','364119'})
 originals={}
 for e in chunks:
  with (I/e['path']).open() as f:
   for line in f:
    x=json.loads(line);n=str(x['mathdb_id'])
    if n in ids:assert n not in originals;originals[n]=x
 assert set(originals)==set(ids)
 assigned=read(R/'assigned-records.json');ds=read(R/'dispositions.json')
 assert len(ds)==50 and [str(x['mathdb_id']) for x in ds]==ids
 assert assigned==[originals[n] for n in ids]
 for d in ds:
  x=originals[str(d['mathdb_id'])]
  assert d['literal_statement']==x['statement']
  assert hashlib.sha256(x['statement'].encode('utf-8')).hexdigest()==d['literal_statement_sha256']
  assert hashlib.sha256(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')).hexdigest()==d['canonical_record_sha256']
  assert d['accepted_credit']==0 and not d['novelty_cleared'] and not d['dependency_closure']
  assert all(d.get(k) for k in ['scope_reason','quantifier_review','mechanism_and_obstacle','primary_level','proof_level','registry_level'])
 assert read(R/'proposals.json')==[]
 for e in read(R/'sourcebytes.json'):check(R/e['path'],e['sha256'],e['size'])
 for e in read(R/'excerpts.json'):
  assert str(e['mathdb_id']) in ids
  lines=(R/e['file']).read_text().splitlines()
  assert e['text']=='\n'.join(lines[e['start_line']-1:e['end_line']])
 if sys.argv[1:]==['--seal']:
  es=[{'path':s,'sha256':digest(R/s),'size':(R/s).stat().st_size} for s in sorted(payload(R)-EXCLUDE)]
  (R/'manifest.json').write_text(json.dumps({'files':es,'excluded_exact_relative_paths':sorted(EXCLUDE)},indent=2)+'\n')
 else:assert not sys.argv[1:]
 m=read(R/'manifest.json');assert set(m['excluded_exact_relative_paths'])==EXCLUDE
 assert payload(R)-EXCLUDE=={e['path'] for e in m['files']}
 for e in m['files']:check(R/e['path'],e['sha256'],e['size'])
 receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'original_bindings':len(refs),'original_corpus_chunks':20,'assigned_literal_statement_screens':50,'baseline_reported_reviews':2433,'other_active_reservations':50,'proposals':0,'retirements':sum(d['disposition'].startswith('RETIRE') for d in ds),'selected_primary_sections_records':sum(d['primary_level']=='selected source body/section read' for d in ds),'current_registry_clearance':False,'independent_mathematical_proof_replay':False,'payload_files':len(m['files']),'manifest_sha256':digest(R/'manifest.json'),'counts_unchanged':{'additional':9,'total':39,'next':40}}
 (R/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
except Exception as e:
 (R/'final-receipt.json').write_text(json.dumps({'status':'FAIL','error':repr(e)})+'\n');raise
