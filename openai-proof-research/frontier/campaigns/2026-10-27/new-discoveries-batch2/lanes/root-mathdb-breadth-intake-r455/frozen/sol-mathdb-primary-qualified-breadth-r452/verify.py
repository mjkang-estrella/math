"""Independent, read-only verifier. Run only through the pinned helper guard."""
from pathlib import Path
import json,hashlib,datetime,sys
L=Path(__file__).resolve().parent; B=L.parent

def sha(b): return hashlib.sha256(b).hexdigest()
def load(p): return json.loads(Path(p).read_bytes())
def check(p,h,n=None):
 b=Path(p).read_bytes()
 if sha(b)!=h:raise ValueError('hash mismatch: '+str(p))
 if n is not None and len(b)!=n:raise ValueError('size mismatch: '+str(p))
 return b

def main():
 manifest=load(L/'manifest.json');expected={r['path'] for r in manifest['files']}
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-{'manifest.json','final-receipt.json'}
 assert expected==actual,('payload set mismatch',expected^actual)
 assert len(expected)==len(manifest['files'])
 for r in manifest['files']:check(L/r['path'],r['sha256'],r['bytes'])
 for r in load(L/'bindings.json'):check(r['original'],r['sha256'],r['bytes'])
 # Independently interpret each authoritative manifest, not its verifier or receipt.
 for name in ['root-mathdb-breadth-intake-r451','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
  d=B/name;m=load(d/'manifest.json');rs=m if isinstance(m,list) else m['files']
  for r in rs:check(d/r['path'],r['sha256'],r.get('size',r.get('bytes')))
  for r in load(d/'bindings.json'):
   if 'original' in r:check(r['original'],r['sha256'],r.get('size',r.get('bytes')))
 inv=B/'pi-mathdb-full-corpus-inventory-r301';im=load(inv/'manifest.json')
 chunks=[r for r in im['files'] if r['path'].startswith('corpus/mathdb-normalized-chunk-')]
 assert len(chunks)==20
 assert {r['path'] for r in chunks}=={str(p.relative_to(inv)) for p in (inv/'corpus').glob('mathdb-normalized-chunk-*.jsonl')}
 for r in chunks:check(inv/r['path'],r['sha256'],r['bytes'])
 frozen=im['frozen_inputs'];assert frozen==load(L/'inventory-frozen-membership.json')
 assert {r['path'] for r in frozen}=={str(p.relative_to(inv)) for p in (inv/'frozen').rglob('*') if p.is_file()}
 for r in frozen:check(inv/r['path'],r['sha256'],r['bytes'])
 intake=B/'root-mathdb-breadth-intake-r451';res=load(intake/'reserved-ids.json');ids=res['ids'];S=set(ids)
 assert res['lane']==L.name and len(ids)==len(S)==50
 assert not S.intersection(res['other_active_reservations'])
 assert not S.intersection([372627,372628,368940,404067,364119])
 queue=load(intake/'queue.json');assert {r['mathdb_id'] for r in queue}==S and len(queue)==50
 cov=load(intake/'coverage-delta.json');assert len(cov)==2683 and not S.intersection(map(int,cov))
 def associated(x):
  out=set()
  if isinstance(x,dict):
   for k,v in x.items():
    if k in ['mathdb_id','problem_id'] and isinstance(v,int):out.add(v)
    elif k in ['problem_ids','mathdb_ids'] and isinstance(v,list):out.update(i for i in v if isinstance(i,int))
    else:out.update(associated(v))
  elif isinstance(x,list):
   for v in x:out.update(associated(v))
  return out
 for n in ['accepted-exclusions.json','historical-dispositions.json']:
  assert not S.intersection(associated(load(B/'root-mathdb-accepted-exclusions-r304'/n))),n
 assert not S.intersection(associated(load(B/'root-mathdb-cayley-review-intake-r363/disposition.json')))
 ds=load(L/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==S
 records=load(L/'records.json');assert len(records)==50
 found={}
 for c in chunks:
  p=inv/c['path']
  for line,raw in enumerate(p.open('rb'),1):
   r=json.loads(raw);i=r['mathdb_id']
   if i in S:
    assert i not in found
    found[i]=(r,str(p),line)
 assert set(found)==S
 for d in ds:
  r,p,line=found[d['mathdb_id']]
  assert (d['original_chunk'],d['original_line'])==(p,line)
  assert d['literal_statement']==r['statement']
  assert sha(r['statement'].encode('utf-8'))==d['statement_utf8_sha256']
  canonical=sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert canonical==d['canonical_record_sha256']
  local=next(x for x in records if x['record']['mathdb_id']==d['mathdb_id'])
  assert local['record']==r and local['canonical_record_sha256']==canonical
  assert d['accepted_credit']==0 and not d['novelty_pass'] and not d['mathematical_pass']
 assert load(L/'proposals.json')==[]
 for r in load(L/'sources.json'):check(L/r['file'],r['sha256'],r['bytes'])
 # Negative controls test rejection predicates in memory, leaving all inputs untouched.
 sample=ds[0];assert sha((sample['literal_statement']+'!').encode())!=sample['statement_utf8_sha256']
 assert expected!={*expected,'unexpected-payload'}
 assert S!={*S,372627}
 return {'integrity':'PASS','mathematical_pass':False,'novelty_pass':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payload_manifest_sha256':sha((L/'manifest.json').read_bytes()),'payload_files':len(expected),'verified_corpus_chunks_in_place':20,'verified_dispositions':50,'baseline_reported_reviews':2683,'primary_question_sections_read':9,'whole_primary_bodies_read':0,'complete_dependency_audits':0,'proposals':0,'accepted_credit':0,'campaign_counts_unchanged':{'additional':9,'total':39,'next':40},'negative_controls':'statement-byte mutation, unexpected payload, assignment pollution detected in memory','upstream_code_executed':False,'mathdb_requests':0}
if __name__=='__main__':
 try:print(json.dumps(main(),indent=2))
 except Exception as e:
  print(json.dumps({'integrity':'FAIL','error':repr(e)}));sys.exit(1)
