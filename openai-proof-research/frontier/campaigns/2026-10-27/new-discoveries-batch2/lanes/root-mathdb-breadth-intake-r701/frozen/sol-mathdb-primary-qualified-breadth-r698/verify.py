import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r697';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch {p}';assert h(b)==e['sha256'],f'hash mismatch {p}'
def exact(root,m):
 names=[e['path'] for e in m['files']];assert len(names)==len(set(names))
 for n in names:assert not pathlib.Path(n).is_absolute() and '..' not in pathlib.Path(n).parts
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==set(names),'extra/missing payload'
 for e in m['files']:check(root/e['path'],e)
def verify():
 m=j(P/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'};exact(P,m)
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');ch=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(ch)==20 and len(cm['frozen_inputs'])==8
 for e in ch+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==8333
 q=j(I/'queue-r698.json');ids={r['mathdb_id'] for r in q};res=j(I/'reserved-ids-r698.json');assert len(q)==len(ids)==50 and ids==set(res['ids'])
 active=j(I/'active-breadth-reservations.json');assert len(active)==3;seen=set()
 for a in active:
  s=set(a['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(a['protected_ids']);seen|=s
 assert ids<=seen
 old=j(L/'root-mathdb-breadth-intake-r695/active-breadth-reservations.json')
 for a in old:
  if a['lane'].endswith(('r628','r696')):
   b=next(b for b in active if a['lane']==b['lane']);assert a['ids']==b['ids']
 for a in active:assert set(a['other_active_reservations'])==seen-set(a['ids'])
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 literals=j(P/'literal-records.json');assert len(literals)==50
 want={}
 for d in ds:
  assert d['classification'] in {'complete','definition-dependent','scope-ambiguous','incomplete'}
  assert d['classification_reason_and_quantifiers'] and d['technical_assessment']
  assert d['complete_self_contained_statement']==(d['classification']=='complete')
  assert d['accepted_credit']==0 and d['current_registry_cleared'] is False
  want.setdefault(d['chunk'],{})[d['line']]=d
 found=set()
 for chunk,ns in want.items():
  assert chunk in {e['path'] for e in ch}
  for n,line in enumerate((C/chunk).open(),1):
   if n not in ns:continue
   r=json.loads(line);d=ns[n];assert r['mathdb_id']==d['mathdb_id'];assert r['statement']==d['statement_utf8'];assert h(r['statement'].encode())==d['statement_sha256'];assert h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())==d['canonical_record_sha256']
   x=next(x for x in literals if x['record']['mathdb_id']==r['mathdb_id']);assert x=={'chunk':chunk,'line':n,'record':r};found.add(r['mathdb_id'])
 assert found==ids and j(P/'proposals.json')==[]
 for e in j(P/'source-provenance.json'):
  assert 'failure' not in e
  pdf=str(e['id'])+('-v2' if e['version']=='1306.0136v2' else '')+'.pdf';check(P/pdf,e);check(P/e['derivative']['path'],e['derivative'])
 if (P/'final-verification-receipt.json').exists():
  r=j(P/'final-verification-receipt.json');check(P/'manifest.json',r['manifest'])
 return {'integrity':'PASS','mathematics_or_novelty_pass':False,'literal_reviews':50,'corpus_chunks':20,'frozen_inputs':8,'direct_pairs':42,'baseline':8333,'proposals':0}
if __name__=='__main__':
 try:
  if len(sys.argv)==3 and sys.argv[1]=='--payload-only':exact(pathlib.Path(sys.argv[2]),j(pathlib.Path(sys.argv[2])/'manifest.json'));print('payload PASS')
  else:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
