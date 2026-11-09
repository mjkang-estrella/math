"""Independent read-only verifier. Run through the fixed helper_guard, python3 -B."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r565';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e,inject=None):
 b=p.read_bytes()
 if inject=='hash':b=bytes([b[0]^1])+b[1:]
 if inject=='size':b+=b'X'
 assert len(b)==e.get('size',e.get('bytes')),'SIZE '+str(p)
 assert h(b)==e['sha256'],'HASH '+str(p)
def exact(root,m,negative=None):
 names={e['path'] for e in m['files']};assert len(names)==len(m['files'])
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 if negative=='extra':actual.add('__injected_extra_payload__')
 assert actual==names,'EXTRA/MISSING '+str(root)
 for i,e in enumerate(m['files']):check(root/e['path'],e,negative if i==0 else None)
def validate():
 check(I/'manifest.json',{'size':10611,'sha256':'a7efa254ea8e6cbddbd51a32484eb7614ba41833b266288f1a9a2a7f3772e49e'})
 exact(I,j(I/'manifest.json'))
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==5083;seen=set()
 active=j(I/'active-breadth-reservations.json');assert len(active)==3
 for r in active:
  s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 res=j(I/'reserved-ids.json');ids=set(res['ids']);assert res['lane']==P.name and len(ids)==50 and ids=={r['mathdb_id'] for r in j(I/'queue.json')}
 assert next(r for r in active if r['lane']==P.name)['ids']==res['ids']
 ds=j(P/'dispositions.json');ar=j(P/'assigned-records.json');assert len(ds)==len(ar)==50 and {r['mathdb_id'] for r in ds}==ids and {r['mathdb_id'] for r in ar}==ids
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),n,r)
 assert len(found)==50
 for d in ds+ar:
  p,n,r=found[d['mathdb_id']];assert d['corpus_chunk']==p and d['corpus_line']==n and d['statement']==r['statement'];assert d['statement_utf8_sha256']==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
 for d in ds:assert d['accepted_credit']==0 and d['current_registry_cleared'] is False and d['technical_screen']
 assert j(P/'proposals.json')==[]
 for e in j(P/'source-provenance.json'):
  check(P/e['file'],e)
  if 'derivative' in e:check(P/e['derivative']['file'],e['derivative'])
 m=j(P/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'}
 exact(P,m,sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None)
 receipt=P/'final-verification-receipt.json'
 if receipt.exists():check(P/'manifest.json',j(receipt)['manifest'])
 return {'integrity':'PASS','literal_reviews':50,'baseline':5083,'prospective_literal_total':5133,'original_chunks':20,'frozen_inputs':8,'active_reservations':150,'flat_bindings':len(j(P/'flat-bindings.json')),'proposals':0,'scientific_acceptance':False,'registry':'HOLD','writes':0}
if __name__=='__main__':
 try:print(json.dumps(validate(),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
