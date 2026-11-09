import pathlib,json,hashlib,sys,copy
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-circulant-13-prior-adjudication-r481';C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 assert p.is_file(),str(p)
 assert p.stat().st_size==e.get('size',e.get('bytes')) and sha(p.read_bytes())==e['sha256'],str(p)
def assignment(ids,other):assert len(ids)==50 and len(set(ids))==50 and not set(ids)&set(other)
def main():
 for e in load(O/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 for e in load(O/'source-bindings.json'):check(pathlib.Path(e['path']),e)
 im=load(I/'manifest.json')['files']
 assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in im}|{'manifest.json','verification-receipt.json'}
 for e in im:check(I/e['path'],e)
 direct=load(I/'bindings.json')
 for e in direct:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=load(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 reservation=load(I/'reserved-ids.json');assert reservation['lane']==O.name
 ids=reservation['ids'];qids=[r['mathdb_id'] for r in load(I/'queue.json')];assert qids==ids
 r484=load(I/'reserved-ids-r484.json');r480=load(L/'root-mathdb-breadth-intake-r479'/'reserved-ids.json')
 other1=r484['ids'];other2=r480['ids'];assert len(other1)==len(other2)==50 and not set(other1)&set(other2)
 assert set(reservation['other_active_reservations'])==set(other1)|set(other2)
 assignment(ids,other1+other2);assert not set(ids)&{372627,372628,368940,404067,364119}
 ds=load(O/'dispositions.json');assert len(ds)==50 and [d['mathdb_id'] for d in ds]==ids
 baseline=load(I/'coverage-delta.json');assert len(baseline)==3333 and not set(map(str,ids))&set(baseline)
 assert load(I/'adjudications.json')['372627']['credit']==0
 assert load(L/'root-mathdb-cayley-review-intake-r363'/'disposition.json')['mathdb_id']==364119
 if '--corrupt-statement' in sys.argv:ds[0]['statement_utf8_sha256']='0'*64
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(r,str(p),n)
 assert len(found)==50
 for d in ds:
  r,p,n=found[d['mathdb_id']];assert (d['original_chunk'],d['original_line'])==(p,n)
  assert d['original_literal_statement']==r['statement'] and d['statement_utf8_sha256']==sha(r['statement'].encode())
  assert d['canonical_record_sha256']==sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert d['accepted_credit']==0 and d['technical_disposition'] and d['evidence_levels']['current_registry'].startswith('HOLD')
 assert load(O/'proposals.json')['qualified_briefs']==[]
 if '--negative' in sys.argv:
  rejected=[]
  try:assignment(ids[:-1]+[other1[0]],other1+other2)
  except AssertionError:rejected.append('other-reservation-overlap')
  d=copy.deepcopy(ds[0]);d['statement_utf8_sha256']='0'*64
  try:assert d['statement_utf8_sha256']==sha(found[d['mathdb_id']][0]['statement'].encode())
  except AssertionError:rejected.append('statement-hash-corruption')
  try:check(O/'assessment.tsv',{'size':0,'sha256':'0'*64})
  except AssertionError:rejected.append('payload-hash-corruption')
  assert len(rejected)==3;print(json.dumps({'bounded_negative_tests':'PASS','rejected':rejected}));return
 manifest=load(O/'manifest.json')['files'];actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()};assert actual=={e['path'] for e in manifest}|{'manifest.json','final-receipt.jsonl'},(actual-{e['path'] for e in manifest})
 for e in manifest:check(O/e['path'],e)
 print(json.dumps({'integrity':'PASS','mathematics_novelty_acceptance':'NOT_CERTIFIED','assignment_count':50,'other_reservations':[len(other1),len(other2)],'chunks':20,'inventory_frozen_inputs':8,'direct_original_copy_bindings':len(direct),'payload_count':len(manifest),'accepted_credit':0}))
if __name__=='__main__':main()
