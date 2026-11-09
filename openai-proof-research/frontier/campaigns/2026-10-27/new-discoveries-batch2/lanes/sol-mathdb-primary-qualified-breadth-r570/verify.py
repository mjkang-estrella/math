"""Independent read-only verifier; invoke under the fixed helper guard. No upstream code executed."""
from pathlib import Path
import json,hashlib,sys,datetime,copy
D=Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r569';C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}'
 assert digest(b)==e['sha256'],f'hash mismatch: {p}'
def payload(base,m,extra=False):
 assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'}
 names=[e['path'] for e in m['files']];assert len(names)==len(set(names))
 actual={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}
 assert all(not p.is_symlink() for p in base.rglob('*'))
 if extra:actual.add('IN_MEMORY_UNEXPECTED_FILE')
 assert actual-set(m['excluded_exact_paths'])==set(names),'extra/missing file'
 for e in m['files']:check(base/e['path'],e)
def verify(negative=None):
 m=load(D/'manifest.json')
 if negative:
  m=copy.deepcopy(m)
  if negative=='hash':m['files'][0]['sha256']='0'*64
  elif negative=='size':m['files'][0]['size']+=1
  elif negative!='extra':raise ValueError(negative)
 payload(D,m,negative=='extra')
 refs=load(D/'flat-bindings.json');assert len(refs)==len({r['path'] for r in refs})
 for e in refs:check(Path(e['path']),e)
 check(I/'manifest.json',dict(size=9785,sha256='965e8fec63f9c16a1cdae1854dc427bdb5c4bf1c7134fe51fda00e230719a3df'))
 im=load(I/'manifest.json');expected={e['path'] for e in im['files']}
 assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected|set(im['excluded_exact_paths'])
 for e in im['files']:check(I/e['path'],e)
 pairs=load(I/'bindings.json')
 for e in pairs:
  check(Path(e['original']),e);check(Path(e['copy']),e)
 check(C/'manifest.json',dict(size=22047,sha256='4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15'))
 cm=load(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 res=load(I/'reserved-ids.json');ids=set(res['ids']);queue=load(I/'queue.json');cov=set(map(int,load(I/'coverage-delta.json')))
 assert len(res['ids'])==len(ids)==50 and res['lane']==D.name and len(cov)==5183
 assert ids=={r['mathdb_id'] for r in queue} and len(queue)==50
 active=load(I/'active-breadth-reservations.json');sets=[set(x['ids']) for x in active]
 assert len(sets)==3 and sum(s==ids for s in sets)==1
 protected={337963,338290,339564,372627,372628,368940,404067,364119,366370,365437,365439,344924}
 for j,s in enumerate(sets):
  assert len(s)==len(active[j]['ids'])==50 and not s&cov and not s&protected
  for t in sets[:j]:assert not s&t
 assert set(res['other_active_reservations'])==set.union(*[s for s in sets if s!=ids])
 records={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line);i=r['mathdb_id']
   if i in ids:
    assert i not in records;records[i]=(r,str(p),n)
 assert set(records)==ids
 assigned=load(D/'assigned-records.json');dis=load(D/'dispositions.json')
 assert len(assigned)==len(dis)==50 and {r['record']['mathdb_id'] for r in assigned}=={r['mathdb_id'] for r in dis}==ids
 for x in assigned:
  i=x['record']['mathdb_id'];r,p,n=records[i];h=digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert x['record']==r and x['chunk']==p and x['line']==n and x['canonical_record_sha256']==h
 for x in dis:
  r,p,n=records[x['mathdb_id']];s=r['statement'];h=digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert x['statement']==s and x['statement_utf8_sha256']==digest(s.encode()) and x['statement_utf8_size']==len(s.encode())
  assert x['canonical_record_sha256']==h and x['chunk']==p and x['line']==n and x['literal_record_read'] is True and x['accepted_credit']==0
 assert load(D/'proposals.json')==[]
 for r in load(D/'source-provenance.json'):
  if 'path' in r:check(Path(r['path']),r);check(Path(r['derivative']['path']),r['derivative'])
 mb=(D/'manifest.json').read_bytes()
 return dict(integrity='PASS',scientific_acceptance=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=digest(mb),manifest_size=len(mb),payload_files=len(m['files']),flat_original_bindings=len(refs),intake_original_copy_pairs=len(pairs),original_chunks=20,frozen_inputs=8,baseline_record_reviews=5183,literal_record_reviews=50,complete_primary_statements_verified=4,proposals=0,reserved_sets_disjoint=3,counts_unchanged='9 additional /39 total /next40',registry='HOLD',command='OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B verify.py')
if __name__=='__main__':
 try:print(json.dumps(verify(sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None),indent=2))
 except Exception as e:print(json.dumps(dict(integrity='FAIL',error=str(e))),file=sys.stderr);sys.exit(1)
