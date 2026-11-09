#!/usr/bin/env python3
"""Independent, read-only verification. Run only via verify.sh (fixed guard)."""
import json, hashlib, sys
from pathlib import Path
P=Path(__file__).resolve().parent
I=P.parent/'root-mathdb-breadth-intake-r679'
R=P.parent/'pi-mathdb-full-corpus-inventory-r301'
def load(p): return json.loads(p.read_text())
def check_bytes(data,e):
 assert len(data)==e.get('size',e.get('bytes')), ('size',e)
 assert hashlib.sha256(data).hexdigest()==e['sha256'], ('hash',e)
def check_file(p,e): check_bytes(p.read_bytes(),e)
def paths_check(actual,expected): assert set(actual)==set(expected), ('exact payload',set(actual)^set(expected))
def canon(r): return hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def payload(base,m):
 excluded=set(m['excluded_exact_paths'])
 paths_check([str(x.relative_to(base)) for x in base.rglob('*') if x.is_file() and str(x.relative_to(base)) not in excluded],[e['path'] for e in m['files']])
 for e in m['files']: check_file(base/e['path'],e)
def main():
 m=load(P/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'};payload(P,m)
 for e in load(P/'flat-bindings.json'):check_file(Path(e['path']),e)
 for e in load(P/'initial-bindings.json'):check_file(Path(e['path']),e)
 payload(I,load(I/'manifest.json'))
 for e in load(I/'bindings.json'):
  check_file(Path(e['original']),e);check_file(Path(e['copy']),e)
 assert (R/'manifest.json').read_bytes()==(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()
 inv=load(R/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:check_file(R/e['path'],e)
 coverage=load(I/'coverage-delta.json');assert len(coverage)==7933
 active=load(I/'active-breadth-reservations.json');assert len(active)==3
 sets=[set(a['ids']) for a in active];protected=set(load(I/'reserved-ids-r682.json')['protected_ids'])
 for n,s in enumerate(sets):
  assert not s&set(map(int,coverage)) and not s&protected
  for t in sets[:n]:assert not s&t
 assigned=load(I/'reserved-ids-r682.json')['ids'];assert len(assigned)==len(set(assigned))==50
 assert set(assigned)=={r['mathdb_id'] for r in load(I/'queue-r682.json')}
 assert set(assigned) in sets
 records=load(P/'literal-records.json');ds=load(P/'dispositions.json');assert len(records)==len(ds)==50
 assert {x['mathdb_id'] for x in records}==set(assigned)=={x['mathdb_id'] for x in ds}
 # Only assigned scientific rows enter the verification map.
 exact={}
 wanted=set(assigned)
 for e in chunks:
  f=R/e['path']
  for n,line in enumerate(f.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in wanted:exact[r['mathdb_id']]=(str(f.resolve()),n,r)
 for x in records:
  chunk,n,r=exact[x['mathdb_id']];assert x['chunk']==chunk and x['line']==n and x['record']==r and x['canonical_record_sha256']==canon(r)
 for x in ds:
  chunk,n,r=exact[x['mathdb_id']]
  assert x['corpus_chunk']==chunk and x['corpus_line']==n and x['statement_utf8']==r['statement']
  assert x['canonical_record_sha256']==canon(r) and x['statement_sha256']==hashlib.sha256(r['statement'].encode()).hexdigest()
  assert x['completeness']['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete']
  assert x['completeness']['reason'] and x['technical_assessment'] and x['credit']==0
 assert len(load(P/'proposals.json'))<=3
 for e in load(P/'derivative-bindings.json'):check_file(P/e['path'],e)
 for e in load(P/'source-provenance.json'):
  if 'path' in e:check_file(P/e['path'],e)
 return dict(integrity='PASS',math_or_novelty_pass=False,literal_reviews=50,baseline=7933,chunks=20,frozen_inputs=8,reservation_sizes=list(map(len,sets)),payload_files=len(m['files']))
def negative_tests():
 e={'size':3,'sha256':hashlib.sha256(b'abc').hexdigest()};out=[]
 for name,fn in [('hash',lambda:check_bytes(b'abd',e)),('size',lambda:check_bytes(b'abcd',e)),('extra_file',lambda:paths_check(['a','extra'],['a']))]:
  try:fn()
  except AssertionError:out.append({'test':name,'rejected':True,'originals_mutated':False})
  else:raise AssertionError('negative accepted: '+name)
 return out
if __name__=='__main__':
 try:print(json.dumps(negative_tests() if '--self-test' in sys.argv else main(),indent=2))
 except Exception as exc:print(str(exc),file=sys.stderr);sys.exit(1)
