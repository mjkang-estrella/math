from pathlib import Path
import hashlib,json,sys,datetime
D=Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r491';C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')) and digest(b)==e['sha256'],'byte mismatch '+str(p)
def main():
 m=load(D/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','verification-receipt.json']
 actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 assert len(m['files'])==len({x['path'] for x in m['files']}) and actual=={x['path'] for x in m['files']},'own payload set mismatch'
 for e in m['files']:check(D/e['path'],e)
 refs=load(D/'flat-bindings.json')
 for e in refs:check(Path(e['path']),e)
 im=load(I/'manifest.json');ia={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(im['excluded_exact_paths'])
 assert ia=={e['path'] for e in im['files']},'intake exact payload mismatch'
 for e in im['files']:check(I/e['path'],e)
 for e in load(I/'bindings.json'):
  check(Path(e['original']),e);check(Path(e['copy']),e)
 cm=load(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')]
 assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 rr=load(I/'reserved-ids.json');ids=set(rr['ids']);others=set(rr['other_active_reservations'])
 assert len(ids)==len(rr['ids'])==50 and len(others)==len(rr['other_active_reservations'])==100
 assert not ids&others and not ids&{372627,372628,368940,404067,364119}
 assert ids=={r['mathdb_id'] for r in load(I/'queue.json')} and len(load(I/'queue.json'))==50
 ds=load(D/'dispositions.json');assert len(ds)==len({r['mathdb_id'] for r in ds})==50 and {r['mathdb_id'] for r in ds}==ids
 originals={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in originals
    originals[r['mathdb_id']]=(r,str(p),n)
 assert len(originals)==50
 if '--negative-statement' in sys.argv:ds[0]['literal_statement']+='x'
 for a in ds:
  r,p,n=originals[a['mathdb_id']]
  assert a['original_chunk']==p and a['original_line']==n,'original locator mismatch'
  assert a['literal_statement']==r['statement'],'literal statement mismatch'
  assert a['statement_utf8_sha256']==digest(r['statement'].encode()),'statement hash mismatch'
  assert a['canonical_record_sha256']==digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'canonical hash mismatch'
  assert a['accepted_credit']==0
 assert load(D/'adjudications-carried.json')==load(I/'adjudications.json')
 assert load(D/'proposals.json')['qualified_briefs']==[]
 cov=load(D/'coverage-provenance.json');assert cov['baseline_reported_reviews']==3533 and cov['new_literal_reviews']==50 and (cov['accepted_additional'],cov['accepted_total'],cov['next'])==(9,39,40)
 return {'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payload_files':len(actual),'actual_flat_references':len(refs),'intake_manifest':'PASS','direct_original_copy_bindings':'PASS','original_chunks':20,'separate_frozen_inputs':8,'assignments':50,'other_reservations':100,'all_literal_canonical_hashes':'PASS','accepted_credit':0,'bounded_negative_test':'See negative-test.json','mathematics_novelty_compliance_pass':False,'upstream_verifiers_executed':False}
try:print(json.dumps(main(),indent=2))
except Exception as e:
 print(json.dumps({'status':'FAIL','error':str(e)}));sys.exit(1)
