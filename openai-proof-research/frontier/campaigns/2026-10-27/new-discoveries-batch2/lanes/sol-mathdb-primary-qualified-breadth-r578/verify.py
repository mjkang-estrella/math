#!/usr/bin/env python3
"""Independent read-only integrity verifier. Run under the fixed helper_guard.py."""
import json,hashlib,sys
from pathlib import Path
D=Path(__file__).resolve().parent;L=D.parent
H=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def checked(p,r):
 b=Path(p).read_bytes()
 assert len(b)==r['size'],'size mismatch: '+str(p)
 assert H(b)==r['sha256'],'hash mismatch: '+str(p)
 return b
def payload(d,m):
 expected={r['path'] for r in m['files']}
 assert len(expected)==len(m['files']),'duplicate manifest entries'
 assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'},'invalid exclusions'
 actual={str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 assert actual==expected,'extra/missing payload: '+str(actual^expected)
 for r in m['files']:checked(d/r['path'],r)
def main():
 m=load(D/'manifest.json');payload(D,m)
 flat=load(D/'flat-bindings.json');paths=[r['path'] for r in flat];assert len(paths)==len(set(paths))
 for r in flat:checked(r['path'],r)
 for intake in ['root-mathdb-breadth-intake-r577','root-mathdb-breadth-intake-r579']:
  d=L/intake;im=load(d/'manifest.json');exp={r['path'] for r in im['files']}
  assert {str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}-set(im['excluded_exact_paths'])==exp
  for r in im['files']:checked(d/r['path'],r)
  for r in load(d/'bindings.json'):checked(r['original'],r);checked(r['copy'],r)
 inv=L/'pi-mathdb-full-corpus-inventory-r301';im=load(inv/'manifest.json');chunks=[r for r in im['files'] if r['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(im['frozen_inputs'])==8
 for r in chunks+im['frozen_inputs']:checked(inv/r['path'],{'size':r['bytes'],'sha256':r['sha256']})
 assigned=load(L/'root-mathdb-breadth-intake-r577/reserved-ids.json')['ids'];assert len(assigned)==len(set(assigned))==50
 assert set(assigned)=={r['mathdb_id'] for r in load(L/'root-mathdb-breadth-intake-r577/queue.json')}
 cov=load(L/'root-mathdb-breadth-intake-r579/coverage-delta.json');assert len(cov)==5433
 oldcov=load(L/'root-mathdb-breadth-intake-r577/coverage-delta.json');assert len(oldcov)==5383 and set(oldcov)<=set(cov)
 res=load(L/'root-mathdb-breadth-intake-r579/active-breadth-reservations.json');seen=set();protected={337963,338290,339564,372627,372628,368940,404067,364119,366370,365437,365439}
 for r in res:
  s=set(r['ids']);assert len(s)==50 and not(s&seen) and not(s&set(map(int,cov))) and not(s&protected);seen|=s
 assert next(r['ids'] for r in res if r['lane']==D.name)==assigned
 assert any(r['lane']=='claude-mathdb-primary-qualified-breadth-r504' and r['status']=='rate_limited_reserved_unreviewed' for r in res)
 rows=load(D/'literal-records.json');dis=load(D/'dispositions.json');assert len(rows)==len(dis)==50
 assert {r['mathdb_id'] for r in rows}=={r['mathdb_id'] for r in dis}==set(assigned)
 got={}
 for c in chunks:
  p=inv/c['path']
  for no,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in assigned:got[r['mathdb_id']]=(str(p),no,r)
 for row in rows:
  p,no,r=got[row['mathdb_id']];assert row['chunk']==p and row['line']==no and row['record']==r and row['statement']==r['statement']
  assert row['statement_sha256']==H(r['statement'].encode('utf-8'))
  assert row['canonical_record_sha256']==H(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  x=next(x for x in dis if x['mathdb_id']==r['mathdb_id']);assert x['statement']==r['statement'] and x['statement_utf8_sha256']==row['statement_sha256'] and x['canonical_record_sha256']==row['canonical_record_sha256']
  assert x['corpus_chunk']==p and x['corpus_line']==no and x['scope_flags'] and x['accepted_credit']==0
 assert len(load(D/'proposals.json'))<=3
 for f in ['source-provenance.json','derivative-bindings.json']:
  for r in load(D/f):
   if 'path' in r:checked(r['path'],r)
 return {'status':'PASS_INTEGRITY_ONLY','manifest_sha256':H((D/'manifest.json').read_bytes()),'manifest_size':(D/'manifest.json').stat().st_size,'exact_payload_files':len(m['files']),'original_chunks':20,'frozen_inputs':8,'assignment':50,'latest_coverage_baseline':5433,'record_reviews_delta':50,'proposals':len(load(D/'proposals.json')),'math_and_novelty_pass':False}
if __name__=='__main__':
 try:print(json.dumps(main(),sort_keys=True))
 except Exception as e:print(str(e),file=sys.stderr);sys.exit(1)
