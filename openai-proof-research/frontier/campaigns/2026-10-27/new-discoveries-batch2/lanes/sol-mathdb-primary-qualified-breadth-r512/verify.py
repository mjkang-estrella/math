"""Independent read-only verification; run through the fixed helper guard. No upstream code execution."""
import pathlib,json,hashlib,datetime,sys
P=pathlib.Path(__file__).resolve().parent
def digest(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def check_bytes(b,e):
 assert len(b)==e.get('size',e.get('bytes')), 'size mismatch'
 assert digest(b)==e['sha256'], 'hash mismatch'
def check_payload(root,m):
 excluded=set(m['excluded_exact_paths']);assert excluded=={'manifest.json','verification-receipt.json'}
 entries=m['files'];names=[e['path'] for e in entries];assert len(names)==len(set(names))
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 assert actual-set(names)<=excluded and set(names)<=actual,'extra/missing payload'
 for e in entries:check_bytes((root/e['path']).read_bytes(),e)
def verify():
 m=load(P/'manifest.json');check_payload(P,m)
 bindings=load(P/'flat-bindings.json');bm={e['path']:e for e in bindings};assert len(bm)==len(bindings)
 for e in bindings:check_bytes(pathlib.Path(e['path']).read_bytes(),e)
 L=P.parent;I=L/'root-mathdb-breadth-intake-r511';C=L/'pi-mathdb-full-corpus-inventory-r301'
 assert bm[str(I/'manifest.json')]['sha256']=='8f5c8b94a76615c305640af91caf1f43ca31fcede1c0ba678d1033e29836cfc6'
 check_payload(I,load(I/'manifest.json'))
 pairs=load(I/'bindings.json')
 for e in pairs:
  a=pathlib.Path(e['original']).read_bytes();b=pathlib.Path(e['copy']).read_bytes();check_bytes(a,e);check_bytes(b,e);assert a==b
 cm=load(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check_bytes((C/e['path']).read_bytes(),e)
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  assert (L/'root-mathdb-accepted-exclusions-r304'/name).read_bytes()==(C/'frozen'/name).read_bytes()
 q=load(I/'queue.json');r=load(I/'reserved-ids.json');cov=load(I/'coverage-delta.json');active=load(I/'active-breadth-reservations.json')
 ids=[e['mathdb_id'] for e in q];assert len(ids)==len(set(ids))==50 and set(ids)==set(r['ids']) and len(cov)==3833
 assert len(active)==3 and next(e['ids'] for e in active if e['lane']==P.name)==ids
 sets=[set(e['ids']) for e in active]
 for j,s in enumerate(sets):
  assert len(s)==50 and not s&set(map(int,cov)) and not s&set(r['protected_ids'])
  for t in sets[j+1:]:assert not s&t
 assert set.union(*(set(e['ids']) for e in active if e['lane']!=P.name))==set(r['other_active_reservations'])
 rows=load(P/'statements.json');ds=load(P/'dispositions.json');assert [e['mathdb_id'] for e in rows]==ids==[e['mathdb_id'] for e in ds]
 found={}
 for e in chunks:
  for line,b in enumerate((C/e['path']).read_bytes().splitlines(),1):
   rec=json.loads(b);i=rec['mathdb_id']
   if i in ids:
    assert i not in found;found[i]=(str(C/e['path']),line,rec)
 assert len(found)==50
 for row,d in zip(rows,ds):
  path,line,rec=found[row['mathdb_id']]
  assert row['record']==rec and row['corpus_path']==path and row['line']==line
  assert row['statement']==rec['statement'] and row['statement_sha256']==digest(rec['statement'].encode('utf-8'))
  assert row['canonical_record_sha256']==digest(json.dumps(rec,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  for k in ['mathdb_id','statement','statement_sha256','canonical_record_sha256','corpus_path','line']:assert row[k]==d[k]
  assert d['technical_assessment'] and d['novelty_cleared'] is False and d['discovery_credit']==0
 proposals=load(P/'proposals.json');assert len(proposals)<=3 and proposals==[]
 for e in load(P/'source-provenance.json'):
  if 'path' in e:
   check_bytes((P/e['path']).read_bytes(),e)
   if 'derivative' in e:check_bytes((P/e['derivative']['path']).read_bytes(),e['derivative'])
 for e in load(P/'visual-bindings.json'):check_bytes((P/e['path']).read_bytes(),e)
 neg=load(P/'negative-tests.json');assert neg['hash_rejected'] and neg['size_rejected'] and neg['extra_file_rejected']
 return {'status':'INTEGRITY_PASS_ONLY','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':{'sha256':digest((P/'manifest.json').read_bytes()),'size':(P/'manifest.json').stat().st_size},'verifier':{'sha256':digest(pathlib.Path(__file__).read_bytes()),'size':pathlib.Path(__file__).stat().st_size},'intake_direct_pairs':len(pairs),'original_corpus_chunks':20,'frozen_inputs':8,'coverage_baseline':3833,'assigned_literal_reviews':50,'primary_passage_rows':8,'whole_body_reviews':0,'dependency_audits':0,'proposals':0,'accepted_credit':0,'negative_tests':neg,'mathematics_novelty_and_registry':'NOT_PASS; see dispositions and source-coverage.json'}
if __name__=='__main__':
 try:
  if len(sys.argv)>1:
   assert sys.argv[1]=='--check-payload';check_payload(pathlib.Path(sys.argv[2]),load(pathlib.Path(sys.argv[2])/'manifest.json'));print('PASS')
  else:print(json.dumps(verify(),indent=2))
 except Exception as e:
  print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
