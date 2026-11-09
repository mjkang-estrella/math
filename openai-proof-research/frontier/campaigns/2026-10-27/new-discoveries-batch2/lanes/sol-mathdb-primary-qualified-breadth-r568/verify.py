"""Independent read-only verification. Run through the fixed helper_guard.py only."""
import pathlib,json,hashlib,sys,itertools
D=pathlib.Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r567'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def sha(b):return hashlib.sha256(b).hexdigest()
def check(b,e):
 assert len(b)==e.get('size',e.get('bytes')),('size',e.get('path'))
 assert sha(b)==e['sha256'],('hash',e.get('path'))
def exact(files,expected,excluded):assert set(files)==set(expected)|set(excluded),'exact file set mismatch'
def load(p):return json.loads(p.read_bytes())
def main():
 manifest=load(D/'manifest.json');expected={e['path']:e for e in manifest['files']}
 assert manifest['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 exact([str(p.relative_to(D)) for p in D.rglob('*') if p.is_file()],expected,manifest['excluded_exact_paths'])
 for n,e in expected.items():check((D/n).read_bytes(),e)
 bindings=load(D/'flat-bindings.json');by={e['path']:e for e in bindings}
 for e in bindings:check(pathlib.Path(e['path']).read_bytes(),e)
 for n in ['manifest.json','queue.json','reserved-ids.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','verify.py','bindings.json','active-breadth-reservations.json']:
  assert str(I/n) in by
 im=load(I/'manifest.json');ex={e['path']:e for e in im['files']}
 exact([str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()],ex,im['excluded_exact_paths'])
 for n,e in ex.items():check((I/n).read_bytes(),e)
 pairs=load(I/'bindings.json')
 for e in pairs:
  a=pathlib.Path(e['original']).read_bytes();b=pathlib.Path(e['copy']).read_bytes();check(a,e);check(b,e);assert a==b
 assert (R/'manifest.json').read_bytes()==(I/'frozen'/R.name/'manifest.json').read_bytes()
 rm=load(R/'manifest.json');chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for e in chunks+rm['frozen_inputs']:check((R/e['path']).read_bytes(),e);assert str(R/e['path']) in by
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  assert (L/'root-mathdb-accepted-exclusions-r304'/name).read_bytes()==(R/'frozen'/name).read_bytes()
 cov=load(I/'coverage-delta.json');assert len(cov)==5133
 res=load(I/'reserved-ids.json');queue=load(I/'queue.json');assigned=set(res['ids']);assert len(assigned)==50 and assigned=={r['mathdb_id'] for r in queue}
 reserved=load(I/'active-breadth-reservations.json');assert len(reserved)==3
 seen=set();covered=set(map(int,cov));protected=set(res['protected_ids']);assert {337963,338290,339564,364119,365437,365439,366370,368940,372627,372628,404067}<=protected
 for r in reserved:
  s=set(r['ids']);assert len(s)==50 and not s&(seen|covered|protected);seen|=s
  assert set(r['other_active_reservations'])==set().union(*(set(q['ids']) for q in reserved if q['lane']!=r['lane']))
 assert res['lane']==D.name and not assigned&(covered|set(res['other_active_reservations'])|protected)
 assert set(res['other_active_reservations'])==seen-assigned
 lit=load(D/'literal-records.json');disp=load(D/'dispositions.json');assert len(lit)==len(disp)==50
 assert {e['mathdb_id'] for e in lit}=={e['mathdb_id'] for e in disp}==assigned
 found={}
 for e in chunks:
  for line,s in enumerate((R/e['path']).open(),1):
   r=json.loads(s)
   if r['mathdb_id'] in assigned:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(R/e['path']),line,r)
 for e in lit:
  path,line,r=found[e['mathdb_id']];assert (e['chunk'],e['line'],e['record'])==(path,line,r)
  assert sha(r['statement'].encode())==e['statement_utf8_sha256']
  assert sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())==e['canonical_record_sha256']
  d=next(q for q in disp if q['mathdb_id']==e['mathdb_id'])
  for k in ['chunk','line','statement_utf8_sha256','canonical_record_sha256']:assert d[k]==e[k]
  assert d['statement']==r['statement'] and d['accepted_credit']==0
 assert load(D/'proposals.json')==[]
 for listname in ['source-provenance.json','derivative-bindings.json']:
  for e in load(D/listname):
   if 'path' in e:check((D/e['path']).read_bytes(),e)
 # Bounded negative checks use synthetic bytes/sets in memory; no original or packet mutation.
 rejected=[]
 e={'size':3,'sha256':sha(b'abc')}
 for name,run in [('hash',lambda:check(b'abd',e)),('size',lambda:check(b'abcd',e)),('extra_file',lambda:exact({'a','extra'},{'a'},set()))]:
  try:run()
  except AssertionError:rejected.append(name)
  else:raise AssertionError('negative not rejected '+name)
 assert len(rejected)==3
 print(json.dumps({'integrity':'PASS','actual_original_copy_pairs':len(pairs),'original_corpus_chunks':20,'inventory_frozen_inputs':8,'coverage_baseline_literal_records':5133,'literal_records':50,'proposals':0,'negative_rejections':rejected,'math_novelty_clearance':False}))
if __name__=='__main__':
 try:main()
 except Exception as ex:print('VERIFY FAIL: '+repr(ex),file=sys.stderr);sys.exit(1)
