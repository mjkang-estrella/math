"""Independent read-only verifier. Run with fixed helper_guard.py and python3 -B.
--negative hash|size|extra injects one in-memory mismatch, writes nothing, and must fail.
Integrity PASS certifies no mathematical or priority gate.
"""
import pathlib,json,hashlib,sys,copy
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r621';C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(p):
 b=p.read_bytes();return hashlib.sha256(b).hexdigest(),len(b)
def check(p,d):
 assert p.is_file() and not p.is_symlink(),str(p)
 assert digest(p)==(d['sha256'],d.get('size',d.get('bytes'))),'hash/size mismatch '+str(p)
def payload(root,m,negative=None):
 entries=copy.deepcopy(m['files']);actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 if negative=='hash':entries[0]['sha256']='0'*64
 if negative=='size':entries[0]['size']=entries[0].get('size',entries[0].get('bytes'))+1
 if negative=='extra':actual.add('__injected_extra_file__')
 expected={x['path'] for x in entries};assert len(expected)==len(entries),'duplicate manifest entry'
 assert actual-set(m['excluded_exact_paths'])==expected,'exact payload mismatch'
 for d in entries:check(root/d['path'],d)
try:
 mode=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None
 assert not sys.argv[1:] or mode in ['hash','size','extra'],'bad arguments'
 m=load(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 payload(P,m,mode)
 refs=load(P/'flat-bindings.json');assert len({x['path'] for x in refs})==len(refs)
 for d in refs:check(pathlib.Path(d['path']),d)
 assert digest(I/'manifest.json')==('69a8ab79efe4eea65f8084c743c0862ee430985e81bec1577930e77ba738e3f3',10440)
 im=load(I/'manifest.json');payload(I,im)
 pairs=load(I/'bindings.json')
 for d in pairs:
  check(pathlib.Path(d['original']),d);check(pathlib.Path(d['copy']),d)
 cm=load(C/'manifest.json');chunks=[x for x in cm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for d in chunks+cm['frozen_inputs']:check(C/d['path'],d)
 # Verify original accepted-exclusions/historical bytes against the separately bound inventory copies.
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  assert digest(L/'root-mathdb-accepted-exclusions-r304'/name)==digest(C/'frozen'/name)
 covered={int(x) for x in load(I/'coverage-delta.json')};assert len(covered)==6483
 reservation=load(I/'reserved-ids-r622.json');ids=set(reservation['ids']);assert len(ids)==50 and reservation['coverage_baseline']==6483 and reservation['lane']==P.name
 queue=load(I/'queue-r622.json');assert {r['mathdb_id'] for r in queue}==ids and len(queue)==50
 active=load(I/'active-breadth-reservations.json');assert len(active)==2
 seen=set();protected=set(reservation['protected_ids']);assert {338366,338408}<=protected
 for a in active:
  s=set(a['ids']);assert len(s)==50 and not(s&seen or s&covered or s&protected);seen|=s
  assert set(a['other_active_reservations'])==set(next(z['ids'] for z in active if z['lane']!=a['lane']))
 assert next(a for a in active if a['lane']==P.name)['ids']==reservation['ids']
 focus=load(I/'focused-assignment.json');assert focus['mathdb_id']==338366 and focus['mathdb_id'] not in seen
 assert not(ids&covered or ids&protected)
 literal=load(P/'literal-records.json');disps=load(P/'dispositions.json');assert len(literal)==len(disps)==50
 assert {x['record']['mathdb_id'] for x in literal}=={x['mathdb_id'] for x in disps}==ids
 found={}
 for d in chunks:
  p=C/d['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found
    found[r['mathdb_id']]=(r,str(p),n)
 for x in literal:
  r=x['record'];id=r['mathdb_id'];assert found[id]==(r,x['chunk'],x['line'])
  canonical=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest();assert canonical==x['canonical_record_sha256']
  d=next(z for z in disps if z['mathdb_id']==id)
  assert (d['chunk'],d['line'],d['statement'],d['canonical_record_sha256'])==(x['chunk'],x['line'],r['statement'],canonical)
  assert d['statement_utf8_sha256']==hashlib.sha256(r['statement'].encode()).hexdigest()
  assert d['literal_statement_completeness']==r['statement_completeness'] and d['literal_status']==r['status']
  assert next(z for z in queue if z['mathdb_id']==id)['statement_completeness']==r['statement_completeness']
  assert d['technical_statement_class'] in ['complete','definition-dependent','ambiguous','incomplete']
  assert d['accepted_credit']==0 and not d['prior_cleared'] and not d['registry_cleared']
 assert load(P/'proposals.json')==[]
 for d in load(P/'source-provenance.json'):check(P/d['file'],d)
 for d in load(P/'derivative-bindings.json'):check(P/d['file'],d)
 if (P/'final-verification-receipt.json').exists():
  r=load(P/'final-verification-receipt.json');assert digest(P/'manifest.json')==(r['manifest_sha256'],r['manifest_size'])
 print(json.dumps({'integrity':'PASS','original_chunks':20,'frozen_inputs':8,'original_copy_pairs':len(pairs),'literal_reviews':50,'baseline':6483,'proposals':0,'mathematical_or_novelty_pass':False}))
except Exception as e:
 print(json.dumps({'integrity':'FAIL','error':type(e).__name__+': '+str(e)}));sys.exit(1)
