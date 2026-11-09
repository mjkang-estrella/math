"""Independent read-only verification. Run via fixed helper_guard; never writes."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r591';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_bytes())
def h(b):return hashlib.sha256(b).hexdigest()
def checkbytes(b,e):
 assert len(b)==e.get('size',e.get('bytes')),'size mismatch'
 assert h(b)==e['sha256'],'hash mismatch'
def check(p,e):checkbytes(p.read_bytes(),e)
def namescheck(actual,expected):assert actual==expected,'exact payload/extra-file mismatch'
def exact(root,m):
 expected={e['path'] for e in m['files']};assert len(expected)==len(m['files'])
 namescheck({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']),expected)
 for e in m['files']:check(root/e['path'],e)
def main():
 m=j(P/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'};exact(P,m)
 for n in ['initial-bindings.json','flat-bindings.json','source-provenance.json']:
  for e in j(P/n):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json')
 for e in pairs:
  check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
 cm=j(C/'manifest.json');assert (C/'manifest.json').read_bytes()==(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()
 chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 for n in ['accepted-exclusions.json','historical-dispositions.json']:
  assert (L/'root-mathdb-accepted-exclusions-r304'/n).read_bytes()==(C/'frozen/root-mathdb-accepted-exclusions-r304'/n).read_bytes()
 cov=j(I/'coverage-delta.json');assert len(cov)==5733
 active=j(I/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==150
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 reservation=j(I/'reserved-ids.json');ids=set(reservation['ids']);assert len(ids)==50 and reservation['lane']==P.name
 assert ids=={r['mathdb_id'] for r in j(I/'queue.json')}
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 found={}
 for e in chunks:
  path=C/e['path']
  for n,line in enumerate(path.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(path,n,r)
 assert len(found)==50
 for d in ds:
  path,n,r=found[d['mathdb_id']]
  assert d['corpus_chunk']==str(path) and d['corpus_line']==n and d['literal_statement']==r['statement']
  assert d['statement_utf8_sha256']==h(r['statement'].encode('utf-8'))
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  assert d['scope_flags']['literal_full_record_read'] and not d['scope_flags']['current_registry_cleared'] and d['accepted_credit']==0
 for d in j(P/'literal-records.json'):
  assert d['record']==found[d['mathdb_id']][2]
 assert j(P/'proposals.json')==[]
 old=j(P/'prior-context-check.json')['preserved_incomplete_rows']
 for i,v in old.items():assert cov[i]==v
 result={'integrity':'PASS','literal_record_reviews':50,'complete_statement_screening':sum(d['complete_self_contained_statement'] for d in ds),'scope_restoration_rows':sum(not d['complete_self_contained_statement'] for d in ds),'original_chunks':20,'frozen_inputs':8,'direct_original_copy_pairs':len(pairs),'reservation_disjointness':True,'reserved_rows':150,'proposals':0,'scientific_acceptance':False,'registry':'HOLD'}
 if '--negative-tests' in sys.argv:
  b=b'bound';e={'size':len(b),'sha256':h(b)};tests=[]
  for label,fn in [('hash',lambda:checkbytes(b'boUnd',e)),('size',lambda:checkbytes(b+b'x',e)),('extra_file',lambda:namescheck({'one','EXTRA'},{'one'}))]:
   try:fn()
   except AssertionError:tests.append({'test':label,'rejected':True})
   else:raise AssertionError('negative accepted '+label)
  result['negative_tests']=tests
 print(json.dumps(result,sort_keys=True))
if __name__=='__main__':
 try:main()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
