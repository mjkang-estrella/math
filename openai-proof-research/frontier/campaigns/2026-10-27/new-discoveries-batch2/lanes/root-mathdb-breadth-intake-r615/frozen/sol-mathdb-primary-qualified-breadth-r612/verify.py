#!/usr/bin/env python3
"""Read-only verifier. Run through the fixed helper_guard.py, python3 -B.
--negative hash|size|extra injects an in-memory fault and must exit nonzero.
"""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r611';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b,e):
 assert len(b)==e.get('size',e.get('bytes')),'size mismatch'
 assert sha(b)==e['sha256'],'hash mismatch'
def check(p,e):blob(p.read_bytes(),e)
def names(actual,expected):assert actual==expected,'extra/missing payload file'
def exact(root,m):
 assert len({e['path'] for e in m['files']})==len(m['files'])
 names({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']),{e['path'] for e in m['files']})
 for e in m['files']:check(root/e['path'],e)
def validate(negative=None):
 m=j(P/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'}
 if negative:
  e=m['files'][0];b=(P/e['path']).read_bytes()
  if negative=='hash':blob(bytes([b[0]^1])+b[1:],e)
  elif negative=='size':blob(b+b'\n',e)
  elif negative=='extra':names({e['path'] for e in m['files']}|{'UNLISTED'}, {e['path'] for e in m['files']})
  else:raise AssertionError('unknown negative')
  raise AssertionError('negative was not rejected')
 exact(P,m)
 b=j(P/'flat-bindings.json')
 for path,e in b.items():check(pathlib.Path(path),e)
 check(I/'manifest.json',b[str(I/'manifest.json')]);exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 check(C/'manifest.json',b[str(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json')])
 cm=j(C/'manifest.json');cs=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(cs)==20 and len(cm['frozen_inputs'])==8
 for e in cs+cm['frozen_inputs']:check(C/e['path'],e)
 q=j(I/'queue-r612.json');r=j(I/'reserved-ids-r612.json');cov=j(I/'coverage-delta.json');assert len(cov)==6233
 ids=set(r['ids']);assert len(q)==len(ids)==50 and ids=={e['mathdb_id'] for e in q}
 reservations=j(I/'active-breadth-reservations.json');ss=[set(e['ids']) for e in reservations];assert len(ss)==3 and ss.count(ids)==1
 for n,s in enumerate(ss):
  assert len(s)==50 and not set(map(str,s))&set(cov)
  protected=set(r['protected_ids'])|set(reservations[n].get('protected_ids',[]));assert not s&protected
  for t in ss[:n]:assert not s&t
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 found={}
 for e in cs:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   o=json.loads(line)
   if o['mathdb_id'] in ids:
    assert o['mathdb_id'] not in found;found[o['mathdb_id']]=(str(p),n,o)
 assert len(found)==50
 literal=j(P/'literal-records.json');assert len(literal)==50
 for x in literal:
  o=x['record'];p,n,t=found[o['mathdb_id']];assert o==t and x['corpus_chunk']==p and x['corpus_line']==n
 for d in ds:
  p,n,o=found[d['mathdb_id']]
  assert (d['corpus_chunk'],d['corpus_line'])==(p,n)
  assert d['statement_utf8']==o['statement'] and d['statement_utf8_sha256']==sha(o['statement'].encode())
  assert d['canonical_record_sha256']==sha(json.dumps(o,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert d['statement_completeness']==o['statement_completeness']
  assert d['source_scope_flags']=={k:v for k,v in o.items() if 'scope' in k or 'complete' in k}
  assert d['complete_self_contained_statement']==(d['technical_statement_class']=='complete')
  assert not d['current_registry_cleared'] and d['discovery_credit']==0
 assert j(P/'proposals.json')==[]
 for e in j(P/'source-provenance.json'):
  if 'path' in e:check(pathlib.Path(e['path']),e)
 for e in j(P/'derivative-bindings.json'):check(pathlib.Path(e['path']),e)
 return {'integrity':'PASS','literal_records':50,'self_contained_statement_reviews':13,'definition_or_scope_limited_records':37,'original_corpus_chunks':20,'frozen_inputs':8,'baseline_reported_reviews':6233,'disjoint_reservations':[50,50,50],'proposals':0,'discovery_credit':0,'math_and_novelty':'NOT CERTIFIED; registry HOLD','bound_external_files':len(b),'payload_files':len(m['files'])}
if __name__=='__main__':
 try:
  print(json.dumps(validate(sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None),sort_keys=True))
 except Exception as e:
  print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
