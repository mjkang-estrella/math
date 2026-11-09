"""Read-only integrity verifier. Run only through the mandated helper guard."""
from pathlib import Path
import json,hashlib,sys
D=Path(__file__).resolve().parent
load=lambda p:json.loads(p.read_text())
def check(p,x):
 b=p.read_bytes();assert len(b)==x.get('size',x.get('bytes')),f'size mismatch: {p}'
 assert hashlib.sha256(b).hexdigest()==x['sha256'],f'hash mismatch: {p}'
def payload(root):
 m=load(root/'manifest.json');excluded={'manifest.json','final-verification-receipt.json'}
 assert set(m['excluded_exact_paths'])==excluded
 entries=m['files'];assert len(entries)==len({x['path'] for x in entries})
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 assert actual=={x['path'] for x in entries}|({'manifest.json','final-verification-receipt.json'}&actual),'extra or missing payload file'
 for x in entries:check(root/x['path'],x)
def verify():
 payload(D);fb=load(D/'flat-bindings.json')
 for p,x in fb.items():check(Path(p),x)
 L=D.parent;I=L/'root-mathdb-breadth-intake-r605';R=L/'pi-mathdb-full-corpus-inventory-r301'
 m=load(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
 for x in m['files']:check(I/x['path'],x)
 for x in load(I/'bindings.json'):
  for k in ['original','copy']:check(Path(x[k]),x)
 rm=load(R/'manifest.json');chunks=[x for x in rm['files'] if x['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for x in chunks+rm['frozen_inputs']:check(R/x['path'],x)
 q=load(I/'queue-r606.json');ids={x['mathdb_id'] for x in q};res=load(I/'reserved-ids-r606.json');assert len(q)==len(ids)==50 and ids==set(res['ids'])
 cov=load(I/'coverage-delta.json');assert len(cov)==6133
 active=load(I/'active-breadth-reservations.json');seen=set();assert len(active)==3
 for x in active:
  s=set(x['ids']);assert len(s)==50 and not s&seen;seen|=s
  assert not s&{int(k) for k in cov}
  assert not s&(set(x['protected_ids'])|{343771,343973,344924,383181})
 assert any(x['lane']==D.name and set(x['ids'])==ids for x in active)
 literal=load(D/'literal-records.json');dis=load(D/'dispositions.json');assert len(dis)==len(literal)==50
 assert {x['mathdb_id'] for x in dis}==ids
 found={}
 for x in chunks:
  p=R/x['path']
  for n,s in enumerate(p.open(),1):
   r=json.loads(s)
   if r.get('mathdb_id') in ids:
    i=r['mathdb_id'];assert i not in found;found[i]=(r,str(p),n)
 assert set(found)==ids
 for x in literal:
  r=x['record'];i=r['mathdb_id'];original,p,n=found[i];assert original==r and (p,n)==(x['chunk'],x['line'])
  h=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest();assert h==x['canonical_record_sha256']
  z=next(v for v in dis if v['mathdb_id']==i)
  assert z['statement_utf8']==r['statement'] and z['statement_utf8_sha256']==hashlib.sha256(r['statement'].encode()).hexdigest()
  assert z['canonical_record_sha256']==h and (z['corpus_chunk'],z['corpus_line'])==(p,n)
  assert z['complete_mathematical_statement_review']==(z['statement_scope']=='complete') and z['discovery_credit']==0
 assert sum(x['complete_mathematical_statement_review'] for x in dis)==20
 assert load(D/'proposals.json')==[]
 for x in load(D/'source-provenance.json'):
  if 'path' in x:check(D/x['path'],x)
 for x in load(D/'derivative-bindings.json'):check(D/x['path'],x)
 # Receipt is excluded from manifest to avoid circularity, but validated if present.
 if (D/'final-verification-receipt.json').exists():
  r=load(D/'final-verification-receipt.json');check(D/'manifest.json',r['manifest'])
 print(json.dumps({'integrity':'PASS','literal_records':50,'complete_statements':20,'incomplete':30,'original_chunks':20,'frozen_inputs':8,'proposals':0,'math_and_novelty':'NOT_CLEARED'}))
if __name__=='__main__':
 try:
  if len(sys.argv)==3 and sys.argv[1]=='--payload-only':payload(Path(sys.argv[2]));print('payload PASS')
  else:verify()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
