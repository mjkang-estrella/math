import pathlib,json,hashlib,datetime,sys,copy
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r703';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),('size',str(p));assert sha(b)==e['sha256'],('hash',str(p))
def exact(root,m):
 names={e['path'] for e in m['files']};assert len(names)==len(m['files'])
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names,('extra/missing',str(root))
 for e in m['files']:check(root/e['path'],e)
def validate_bytes(payload,entries):
 assert set(payload)=={e['path'] for e in entries}
 for e in entries:
  b=payload[e['path']];assert len(b)==e['size'];assert sha(b)==e['sha256']
def main():
 m=j(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(P,m)
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');assert (C/'manifest.json').read_bytes()==(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()
 chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==8483
 active=j(I/'active-breadth-reservations.json');seen=set()
 for a in active:
  ids=set(a['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(a['protected_ids']);seen|=ids
 assert len(active)==3 and len(seen)==150
 assert any(a['lane']=='claude-mathdb-primary-qualified-breadth-r628' and a['status']=='rate_limit_held_not_reconciled' for a in active)
 assert any(a['lane']=='sol-mathdb-primary-qualified-breadth-r702' for a in active)
 ids=set(j(I/'reserved-ids-r704.json')['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue-r704.json')}
 ds=j(P/'dispositions.json');assert len(ds)==50 and len({d['mathdb_id'] for d in ds})==50 and {d['mathdb_id'] for d in ds}==ids
 original={}
 for e in chunks:
  for n,line in enumerate((C/e['path']).open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in original;original[r['mathdb_id']]=(e['path'],n,r)
 literals={x['mathdb_id']:x for x in j(P/'literal-records.json')};assert set(literals)==ids
 for d in ds:
  ck,n,r=original[d['mathdb_id']];assert d['corpus_chunk']==ck and d['corpus_line']==n
  assert d['exact_utf8_statement']==r['statement'] and d['statement_utf8_sha256']==sha(r['statement'].encode())
  assert d['canonical_record_sha256']==sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert literals[d['mathdb_id']]['record']==r
  assert d['classification'] in {'complete','definition-dependent','scope-ambiguous','incomplete'} and d['classification_reason'] and d['technical_assessment']
  assert d['accepted_credit']==0 and not d['current_registry_cleared']
 assert j(P/'proposals.json')==[]
 for e in j(P/'source-provenance.json'):
  if 'failure' in e:continue
  name=str(e['mathdb_id']) if e['version'] in {'1809.07360v1','1907.09451v1','1909.11726v1'} else e['version']
  check(P/(name+'.pdf'),e);check(P/e['derivative']['path'],e['derivative'])
 # Bounded in-memory negative mutations use the same exact payload predicate, touching no originals.
 entries=[{'path':'a','size':3,'sha256':sha(b'abc')}];validate_bytes({'a':b'abc'},entries);neg={}
 for name,payload in [('hash',{'a':b'abd'}),('size',{'a':b'abcd'}),('extra_file',{'a':b'abc','extra':b'x'})]:
  try:validate_bytes(payload,entries)
  except AssertionError:neg[name]='rejected'
  else:raise AssertionError('negative accepted '+name)
 b=(P/'manifest.json').read_bytes()
 return {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','mathematics_and_novelty':'NOT_CERTIFIED','manifest':{'sha256':sha(b),'size':len(b)},'literal_reviews':50,'original_chunks_verified_in_place':20,'separate_frozen_inputs_verified':8,'baseline':8483,'reserved_disjoint_ids':150,'proposals':0,'credit':0,'negative_tests':neg,'negative_method':'bounded in-memory hash/size/extra-file mutations using exact payload predicate; no originals mutated','verifier_read_only':True}
if __name__=='__main__':
 try:print(json.dumps(main(),indent=2))
 except Exception as e:print('FAIL '+repr(e),file=sys.stderr);sys.exit(1)
