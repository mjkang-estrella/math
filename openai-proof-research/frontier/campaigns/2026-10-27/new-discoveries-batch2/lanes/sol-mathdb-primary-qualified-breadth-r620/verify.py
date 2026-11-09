"""Independent read-only verifier. Optional alternate payload directory supports negative fixtures."""
from pathlib import Path
import json,hashlib,sys
P=Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r619';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes()
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch '+str(p))
 if h(b)!=e['sha256']:raise ValueError('hash mismatch '+str(p))
def exact(root,m):
 names=[e['path'] for e in m['files']]
 assert len(names)==len(set(names))
 assert set(m['excluded_exact_paths'])=={'manifest.json',m.get('receipt_name','verification-receipt.json')}
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 if actual-set(m['excluded_exact_paths'])!=set(names):raise ValueError('extra/missing payload file')
 for e in m['files']:check(root/e['path'],e)
def validate(root):
 exact(root,j(root/'manifest.json'))
 check(I/'manifest.json',{'size':10108,'sha256':'a822fe2bd22562b647b3521fcc2d999495d5359e5c56eedfbc16e0cbdf65b961'})
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(Path(e[k]),e)
 flat=j(root/'flat-bindings.json');assert len(flat)==134
 for e in flat:check(Path(e['path']),e)
 cm=j(C/'manifest.json');ce=[e for e in cm['files'] if e['path'].startswith('corpus/')]
 assert len(ce)==20 and len(cm['frozen_inputs'])==8
 for e in ce+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==6433
 active=j(I/'active-breadth-reservations.json');assert len(active)==2
 ids=set(j(I/'reserved-ids-r620.json')['ids']);q=j(I/'queue-r620.json')
 assert len(ids)==len(q)==50 and ids=={r['mathdb_id'] for r in q}
 assert {a['lane'] for a in active}=={'sol-mathdb-primary-qualified-breadth-r616','sol-mathdb-primary-qualified-breadth-r620'}
 seen=set()
 for a in active:
  s=set(a['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&{338366,338408}
  seen|=s
 assert ids<=seen
 found={}
 for e in ce:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found
    found[r['mathdb_id']]=(p,n,r)
 assert len(found)==50
 ds=j(root/'dispositions.json');ls=j(root/'literal-records.json')
 assert len(ds)==len(ls)==50 and {d['mathdb_id'] for d in ds}==ids
 assert {d['mathdb_id'] for d in ls}==ids
 for d in ds:
  p,n,r=found[d['mathdb_id']]
  assert d['corpus_chunk']==str(p) and d['corpus_line']==n
  assert d['exact_utf8_statement']==r['statement']
  assert d['statement_utf8_sha256']==h(r['statement'].encode())
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert d['accepted_credit']==0 and not d['current_registry_cleared']
  assert d['complete_mathematical_statement_review']==(d['technical_statement_class']=='complete')
 for d in ls:
  p,n,r=found[d['mathdb_id']]
  assert d['record']==r and d['corpus_line']==n and d['corpus_chunk']==str(p)
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert d['statement_utf8_sha256']==h(r['statement'].encode())
 assert j(root/'proposals.json')==[]
 for d in j(root/'source-provenance.json'):
  assert d['status']==200 and d['headers']=={'User-Agent':'Mozilla/5.0','Accept':'application/pdf'}
  check(root/(d['name']+'.pdf'),d)
 for e in j(root/'derivative-bindings.json'):check(root/e['path'],e)
 return {'integrity':'PASS','literal_records':50,'corpus_chunks':20,'frozen_inputs':8,'direct_original_copy_pairs':len(j(I/'bindings.json')),'baseline':6433,'breadth_reservations':2,'proposals':0,'mathematics_novelty_pass':False}
if __name__=='__main__':
 try:print(json.dumps(validate(Path(sys.argv[1]).resolve() if len(sys.argv)>1 else P),sort_keys=True))
 except Exception as e:
  print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
