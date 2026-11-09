"""Independent read-only verification. Run only through the fixed helper guard."""
import pathlib,json,hashlib,sys,datetime
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-ordinal-exclusion-intake-r529';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes()
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch '+str(p))
 if digest(b)!=e['sha256']:raise ValueError('hash mismatch '+str(p))
def exact(root,m):
 names=[e['path'] for e in m['files']]
 if len(set(names))!=len(names):raise ValueError('duplicate payload paths')
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 if actual-set(m['excluded_exact_paths'])!=set(names):raise ValueError('extra/missing payload')
 for e in m['files']:check(root/e['path'],e)
def verify():
 check(I/'manifest.json',{'size':13187,'sha256':'c4c4b1b8d85807379b9077ff910ec1e9190728f20ce54f393d3849320625e67a'})
 exact(I,j(I/'manifest.json'))
 flat=j(D/'flat-bindings.json')
 for p,e in flat.items():check(pathlib.Path(p),e)
 pairs=j(I/'bindings.json')
 for e in pairs:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 inventory=C/'manifest.json'
 assert str(inventory) in flat
 # Require inventory binding to the actual intake original/copy pair, not just our flat list.
 binding=next(e for e in pairs if e['original']==str(inventory));check(inventory,binding)
 cm=j(inventory);chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4233
 active=j(I/'active-breadth-reservations.json');assert len(active)==2
 seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and len(r['ids'])==50
  assert not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 res=j(I/'reserved-ids.json');ids=set(res['ids']);assert res['lane']==D.name and res['coverage_baseline']==4233
 assert ids=={e['mathdb_id'] for e in j(I/'queue.json')}
 assert ids==set(next(e for e in active if e['lane']==D.name)['ids'])
 assigned=j(D/'assigned-records.json');disps=j(D/'dispositions.json')
 assert len(assigned)==len(disps)==50 and {e['mathdb_id'] for e in disps}==ids
 assert len({e['mathdb_id'] for e in assigned})==50
 ds={e['mathdb_id']:e for e in disps};records={}
 for e in chunks:
  p=C/e['path']
  for ln,line in enumerate(p.open(),1):
   r=json.loads(line);i=r['mathdb_id']
   if i in ids:
    assert i not in records;records[i]=(str(p),ln,r)
 assert set(records)==ids
 for a in assigned:
  i=a['mathdb_id'];p,ln,r=records[i];d=ds[i]
  assert a['record']==r and a['corpus_path']==p and a['line']==ln
  h=digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  assert a['record_sha256']==d['canonical_record_sha256']==h
  assert d['corpus_path']==p and d['corpus_line']==ln
  assert d['statement_utf8']==r['statement'] and d['statement_utf8_sha256']==digest(r['statement'].encode('utf-8'))
  assert d['technical_read'] and d['credit']==0
 assert j(D/'proposals.json')==[]
 for fn in ['retrieval-bindings.json','derivative-bindings.json']:
  for e in j(D/fn):
   if 'path' in e:check(D/e['path'],e)
 m=j(D/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(D,m)
 return {'integrity':'PASS','mathematics_or_novelty_pass':False,'original_chunks_checked':20,'frozen_inputs_checked':8,'intake_original_copy_pairs':len(pairs),'flat_references_checked':len(flat),'breadth_reservations':2,'baseline_literal_reviews':4233,'literal_statement_reviews':50,'primary_selected_passage_records':8,'primary_bodies_selected':6,'whole_bodies_reviewed':0,'proposals':0,'disjoint':True,'payload_files':len(m['files'])}
if __name__=='__main__':
 try:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
