#!/usr/bin/env python3
import pathlib,json,hashlib,sys,datetime
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r695';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size {p}';assert sha(b)==e['sha256'],f'hash {p}'
def payload(root):
 m=load(root/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 expected={e['path'] for e in m['files']};assert len(expected)==len(m['files'])
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};assert actual-{'manifest.json','final-verification-receipt.json'}==expected,'extra/missing payload'
 for e in m['files']:check(root/e['path'],e)
try:
 if len(sys.argv)>1:
  assert sys.argv[1]=='--payload-only';payload(pathlib.Path(sys.argv[2]));print('{"payload":"PASS"}');sys.exit(0)
 payload(O)
 for e in load(O/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 im=load(I/'manifest.json');expected={e['path'] for e in im['files']}
 assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected|{'manifest.json','verification-receipt.json'}
 for e in im['files']:check(I/e['path'],e)
 for e in load(I/'bindings.json'):
  check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
 inv=load(R/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:check(R/e['path'],e)
 cov=set(map(int,load(I/'coverage-delta.json')));assert len(cov)==8283
 res=load(I/'active-breadth-reservations.json');own=load(I/'reserved-ids-r696.json');protected=set(own['protected_ids'])
 assert own['coverage_baseline']==8283 and own['active_hypothesis_ids']==[] and len(res)==3
 for n,a in enumerate(res):
  s=set(a['ids']);assert len(s)==50 and not s&cov and not s&protected
  for b in res[n+1:]:assert not s&set(b['ids'])
 ids=set(own['ids']);assert ids=={x['mathdb_id'] for x in load(I/'queue-r696.json')}
 assert next(a['ids'] for a in res if a['lane']==O.name)==own['ids']
 d=load(O/'dispositions.json');literal=load(O/'literal-records.json');assert len(d)==len(literal)==50 and {x['mathdb_id'] for x in d}==ids
 by={x['mathdb_id']:x for x in d}
 for x in literal:
  p=pathlib.Path(x['chunk']);assert p in {R/e['path'] for e in chunks}
  with p.open('rb') as h:
   for n,b in enumerate(h,1):
    if n==x['line']:break
   else:raise AssertionError('missing line')
  r=json.loads(b);assert r==x['record'];assert sha(b)==x['line_sha256']
  canon=sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert canon==x['canonical_record_sha256']
  z=by[r['mathdb_id']];assert z['statement']==r['statement'] and z['canonical_record_sha256']==canon and z['statement_utf8_sha256']==sha(r['statement'].encode())
  assert z['corpus_chunk']==str(p) and z['corpus_line']==n and z['corpus_line_sha256']==sha(b)
  assert z['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete'] and z['classification_reason'] and z['technical_assessment'] and z['quantifiers']
  assert z['accepted_credit']==0 and z['novelty_cleared']==False
 assert load(O/'proposals.json')==[]
 for e in load(O/'source-provenance.json'):
  check(O/(str(e['mathdb_id'])+'.pdf'),e);check(pathlib.Path(e['derivative']['path']),e['derivative'])
 print(json.dumps({'integrity':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_original_copy_pairs':len(load(I/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'exact_assigned_literal_reviews':50,'classifications':load(O/'source-coverage.json')['classification_counts'],'baseline_literal_reviews':8283,'proposals':0,'credit':0,'registry':'HOLD','math_novelty_pass':False,'manifest':{'sha256':sha((O/'manifest.json').read_bytes()),'size':(O/'manifest.json').stat().st_size}},indent=2))
except Exception as e:
 print(json.dumps({'integrity':'FAIL','error':str(e)}),file=sys.stderr);sys.exit(1)
