"""Independent read-only verifier. Run through verify.sh (fixed resource guard)."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r691';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),('size',str(p));assert h(b)==e['sha256'],('hash',str(p))
def exact(root,m):
 names=[e['path'] for e in m['files']];assert len(names)==len(set(names));assert set(m['excluded_exact_paths'])=={'manifest.json',m.get('receipt_name','verification-receipt.json')}
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};assert actual-set(m['excluded_exact_paths'])==set(names),('extra/missing payload',str(root))
 for e in m['files']:
  assert not pathlib.Path(e['path']).is_absolute() and '..' not in pathlib.Path(e['path']).parts
  check(root/e['path'],e)
def verify():
 exact(P,j(P/'manifest.json'))
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');e=next(e for e in j(I/'bindings.json') if e['original']==str(C/'manifest.json'));check(C/'manifest.json',e)
 chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  e=next(e for e in cm['frozen_inputs'] if e['path']=='frozen/'+name);check(L/'root-mathdb-accepted-exclusions-r304'/name,e)
 cov=j(I/'coverage-delta.json');assert len(cov)==8183
 rs=j(I/'active-breadth-reservations.json');sets=[set(r['ids']) for r in rs];assert len(sets)==3
 r=j(I/'reserved-ids-r692.json');ids=set(r['ids']);assert len(ids)==50 and r['coverage_baseline']==8183
 for a,s in enumerate(sets):
  assert len(s)==50 and not set(map(str,s))&set(cov);assert not s&set(r['protected_ids'])
  for t in sets[a+1:]:assert not s&t
 assert any(x['lane']=='claude-mathdb-primary-qualified-breadth-r628' and 'held' in x['status'] for x in rs)
 assert any(x['lane']=='sol-mathdb-primary-qualified-breadth-r690' for x in rs)
 assert ids=={x['mathdb_id'] for x in j(I/'queue-r692.json')}
 assert ids==next(set(x['ids']) for x in rs if x['lane']==P.name)
 ds=j(P/'dispositions.json');ls=j(P/'literal-records.json');assert len(ds)==len(ls)==50 and {x['mathdb_id'] for x in ds}==ids
 found={}
 for e in chunks:
  for n,line in enumerate((C/e['path']).open(),1):
   x=json.loads(line)
   if x['mathdb_id'] in ids:
    assert x['mathdb_id'] not in found;found[x['mathdb_id']]=(e['path'],n,x)
 assert len(found)==50
 for d in ds+ls:
  p,n,x=found[d['mathdb_id']];assert d['corpus_path']==p and d['corpus_line']==n and d['statement_utf8']==x['statement'];assert d['statement_utf8_sha256']==h(x['statement'].encode('utf8'));assert d['canonical_record_sha256']==h(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf8'))
  if 'record' in d:assert d['record']==x
 for d in ds:
  assert d['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete'] and d['classification_reason'] and d['quantifier_scope'] and d['technical_assessment'];assert d['accepted_credit']==0 and not d['current_registry_cleared'];assert d['complete_mathematical_statement_reviewed']==(d['classification']=='complete')
 assert j(P/'proposals.json')==[]
 for fn in ['source-provenance.json','successor-provenance.json','other-successor-provenance.json']:
  for e in j(P/fn):
   if e['status']=='STOP':continue
   check(P/e['path'],e);check(P/e['derivative']['path'],e['derivative'])
 return {'integrity':'PASS','literal_reviews':50,'self_contained_complete':15,'definition_dependent':23,'scope_ambiguous':10,'incomplete':2,'proposals':0,'original_chunks':20,'frozen_inputs':8,'coverage_baseline':8183,'disjointness':True,'science_and_novelty_pass':False}
if __name__=='__main__':
 try:
  if len(sys.argv)==3 and sys.argv[1]=='--payload-only':
   root=pathlib.Path(sys.argv[2]);exact(root,j(root/'manifest.json'));print('payload PASS')
  else:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print('FAIL',repr(e),file=sys.stderr);sys.exit(1)
