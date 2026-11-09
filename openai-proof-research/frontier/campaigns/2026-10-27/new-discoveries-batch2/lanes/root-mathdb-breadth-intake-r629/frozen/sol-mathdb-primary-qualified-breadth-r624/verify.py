"""Independent read-only integrity check. No upstream code is imported or run."""
from pathlib import Path
import json,hashlib,sys
D=Path(__file__).resolve().parent
EXCLUDED={'manifest.json','final-verification-receipt.json'}
def j(p):return json.loads(p.read_text())
def check(p,h,n):
 b=p.read_bytes();assert len(b)==n,('size',str(p));assert hashlib.sha256(b).hexdigest()==h,('hash',str(p))
def payload(root):
 m=j(root/'manifest.json');assert set(m['excluded_exact_paths'])==EXCLUDED
 names=[x['path'] for x in m['files']];assert len(names)==len(set(names))
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 assert actual-set(m['excluded_exact_paths'])==set(names),('extra or missing payload',actual-set(names)-EXCLUDED)
 for x in m['files']:check(root/x['path'],x['sha256'],x['size'])
def verify():
 payload(D);L=D.parent;I=L/'root-mathdb-breadth-intake-r623';R=L/'pi-mathdb-full-corpus-inventory-r301'
 refs=j(D/'flat-bindings.json');bound={x['path'] for x in refs}
 for x in refs:check(Path(x['path']),x['sha256'],x['size'])
 check(I/'manifest.json','f92ea754d0c51662aea1b2372fbe76a7eeeb3e8521dc10106900651d3af82d89',10620)
 im=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in im['files']}|set(im['excluded_exact_paths'])
 for x in im['files']:check(I/x['path'],x['sha256'],x['size'])
 for x in j(I/'bindings.json'):
  for k in ['original','copy']:check(Path(x[k]),x['sha256'],x['bytes'])
 rm=j(R/'manifest.json');chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for x in chunks+rm['frozen_inputs']:
  assert str(R/x['path']) in bound;check(R/x['path'],x['sha256'],x['bytes'])
 for n in ['accepted-exclusions.json','historical-dispositions.json']:
  assert (L/'root-mathdb-accepted-exclusions-r304'/n).read_bytes()==(R/'frozen'/n).read_bytes()
 cov=set(map(int,j(I/'coverage-delta.json')));assert len(cov)==6533
 reservations=j(I/'active-breadth-reservations.json');assert len(reservations)==2
 allids=set()
 for a in reservations:
  s=set(a['ids']);assert len(s)==50;assert not s&cov and not s&allids and not s&set(a['protected_ids']);allids|=s
 own=j(I/'reserved-ids-r624.json');ids=set(own['ids']);assert own['coverage_baseline']==6533 and own['lane']==D.name
 assert ids==set(next(a for a in reservations if a['lane']==D.name)['ids'])=={x['mathdb_id'] for x in j(I/'queue-r624.json')}
 assert {338366,338408}<=set(own['protected_ids']);assert j(I/'focused-assignment.json')['mathdb_id']==338366
 ds=j(D/'dispositions.json');ls=j(D/'literal-records.json');assert len(ds)==len(ls)==50
 assert {x['mathdb_id'] for x in ds}==ids and len({x['mathdb_id'] for x in ds})==50
 literals={x['record']['mathdb_id']:x for x in ls};disps={x['mathdb_id']:x for x in ds};found=set()
 for c in chunks:
  p=R/c['path']
  with p.open('rb') as f:
   for ln,b in enumerate(f,1):
    r=json.loads(b);id=r['mathdb_id']
    if id not in ids:continue
    assert id not in found;found.add(id);x=literals[id];d=disps[id]
    h=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    assert x['record']==r and x['chunk']==str(p) and x['line']==ln
    assert x['canonical_record_sha256']==d['canonical_record_sha256']==h
    assert x['literal_line_sha256']==d['literal_line_sha256']==hashlib.sha256(b).hexdigest()
    assert d['corpus_chunk']==str(p) and d['corpus_line']==ln
    assert d['exact_utf8_statement']==r['statement'] and d['statement_sha256']==hashlib.sha256(r['statement'].encode()).hexdigest()
    assert d['complete']==(d['technical_statement_scope']=='complete')
    assert d['incomplete']==(d['technical_statement_scope']=='incomplete')
    assert d['scope_ambiguous']==(d['technical_statement_scope']=='scope-ambiguous')
    assert isinstance(d['definition_dependent'],bool) and d['quantifiers_and_scope'] and d['individual_disposition']
    assert d['accepted_credit']==0 and not d['registry_clearance'] and not d['prior_cleared']
 assert found==ids
 assert j(D/'proposals.json')==[]
 return {'integrity':'PASS','mathematics':'NOT CERTIFIED','novelty':'HOLD','literal_records':50,'complete':10,'incomplete':22,'scope_ambiguous':18,'chunks':20,'frozen_inputs':8,'baseline':6533,'proposals':0}
if __name__=='__main__':
 try:
  if len(sys.argv)==3 and sys.argv[1]=='--payload-only':payload(Path(sys.argv[2]));print('PASS')
  else:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print(repr(e),file=sys.stderr);sys.exit(1)
