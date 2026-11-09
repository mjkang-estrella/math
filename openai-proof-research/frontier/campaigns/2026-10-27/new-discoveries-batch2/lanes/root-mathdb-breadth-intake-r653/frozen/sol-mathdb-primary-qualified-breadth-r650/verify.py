"""Independent read-only verifier. Invoke via verify.sh; no upstream verifier executed."""
import pathlib,json,hashlib,sys,collections
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r649'
def load(p):return json.loads(pathlib.Path(p).read_text())
def digest(p):
 b=pathlib.Path(p).read_bytes();return hashlib.sha256(b).hexdigest(),len(b)
def check(p,h,n):assert digest(p)==(h,n),f'hash/size mismatch: {p}'
def main():
 m=load(D/'manifest.json');entries=[dict(x) for x in m['files']]
 actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file()};excluded={'manifest.json','final-verification-receipt.json'}
 neg=sys.argv[1:] if len(sys.argv)>1 else []
 if neg==['--negative-hash']:entries[0]['sha256']='0'*64
 if neg==['--negative-size']:entries[0]['size']+=1
 if neg==['--negative-extra']:actual.add('UNLISTED-NEGATIVE.txt')
 assert set(m['excluded_exact_paths'])==excluded
 assert actual-{*excluded}=={e['path'] for e in entries},'exact payload extra/missing file'
 assert len(entries)==len({e['path'] for e in entries})
 for e in entries:check(D/e['path'],e['sha256'],e['size'])
 for e in load(D/'flat-bindings.json'):check(e['path'],e['sha256'],e['size'])
 check(I/'manifest.json','4671db8c05084f8dbe2865c1cb54615f15ab38f23edceda8c067c1d354f9c6ee',11223)
 im=load(I/'manifest.json');ip={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}
 assert ip=={x['path'] for x in im['files']}|{'manifest.json','verification-receipt.json'}
 for e in im['files']:check(I/e['path'],e['sha256'],e['size'])
 pairs=load(I/'bindings.json')
 for e in pairs:
  for key in ['original','copy']:check(e[key],e['sha256'],e['bytes'])
 inv=L/'pi-mathdb-full-corpus-inventory-r301/manifest.json';check(inv,'4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15',22047)
 inventory=load(inv);chunks=[r for r in inventory['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(inventory['frozen_inputs'])==8
 for e in chunks+inventory['frozen_inputs']:check(inv.parent/e['path'],e['sha256'],e['bytes'])
 coverage=load(I/'coverage-delta.json');assert len(coverage)==7133
 active=load(I/'active-breadth-reservations.json');union=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50;assert not ids&union;assert not ids&set(map(int,coverage));assert not ids&set(r['protected_ids']);union|=ids
  assert set(r['other_active_reservations'])==set(i for s in active if s['lane']!=r['lane'] for i in s['ids'])
 q=load(I/'queue-r650.json');res=load(I/'reserved-ids-r650.json');ids={r['mathdb_id'] for r in q};assert len(q)==50 and len(ids)==50 and ids==set(res['ids'])
 assert ids==set(next(r for r in active if r['lane']==D.name)['ids'])
 literals=load(D/'literal-records.json');disps=load(D/'dispositions.json');assert len(literals)==len(disps)==50;assert ids=={r['record']['mathdb_id'] for r in literals}=={r['mathdb_id'] for r in disps}
 byid={r['mathdb_id']:r for r in disps};cache={}
 for x in literals:
  p=pathlib.Path(x['chunk']);assert p in [inv.parent/e['path'] for e in chunks]
  if p not in cache:cache[p]=p.read_text().splitlines()
  record=json.loads(cache[p][x['line']-1]);assert record==x['record'];i=record['mathdb_id'];d=byid[i]
  canonical=hashlib.sha256(json.dumps(record,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
  assert canonical==x['canonical_record_sha256']==d['canonical_record_sha256']
  assert record['statement']==d['statement']==d['quantifier_scope']
  assert hashlib.sha256(d['statement'].encode()).hexdigest()==d['statement_utf8_sha256']
  assert d['chunk']==str(p) and d['line']==x['line'];assert d['completeness_classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete'];assert d['completeness_reason'] and d['technical_disposition']
  assert d['accepted_credit']==0 and not d['current_registry_cleared']
 assert len(load(D/'proposals.json'))<=3
 for r in load(D/'source-provenance.json'):
  if 'path' in r:check(r['path'],r['sha256'],r['size'])
 image=load(D/'image-binding.json');check(image['path'],image['sha256'],image['size'])
 # Check original administrative exclusions without borrowing an upstream judgment.
 def ids_in(x):
  if isinstance(x,dict):
   for k,v in x.items():
    if k in ['mathdb_id','mathdb_related_id'] and isinstance(v,int):yield v
    elif k in ['mathdb_ids','problem_ids'] and isinstance(v,list):yield from (i for i in v if isinstance(i,int))
    else:yield from ids_in(v)
  elif isinstance(x,list):
   for y in x:yield from ids_in(y)
 excluded_ids=set()
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  orig=L/'root-mathdb-accepted-exclusions-r304'/name;frozen=inv.parent/'frozen'/name;assert digest(orig)==digest(frozen);excluded_ids.update(ids_in(load(orig)))
 assert not ids&excluded_ids
 return {'integrity':'PASS','scientific_acceptance':False,'original_chunks':20,'frozen_inputs':8,'original_copy_pairs':len(pairs),'baseline':7133,'new_literal_reviews':50,'proposals':len(load(D/'proposals.json')),'classifications':dict(collections.Counter(r['completeness_classification'] for r in disps)),'reservation_disjointness':True,'exact_payload':True}
if __name__=='__main__':
 try:print(json.dumps(main(),sort_keys=True))
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
