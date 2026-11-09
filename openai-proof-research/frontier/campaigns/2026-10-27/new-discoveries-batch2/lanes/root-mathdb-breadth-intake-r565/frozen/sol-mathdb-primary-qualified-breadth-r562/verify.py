"""Independent read-only verifier. Run through the fixed helper_guard.py. No upstream code execution."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r561';C=L/'pi-mathdb-full-corpus-inventory-r301'
mode=sys.argv[1] if len(sys.argv)>1 else ''
def digest(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_text())
def check(p,e):
 b=p.read_bytes()
 if p==P/'proposals.json' and mode=='--negative-hash':b=bytes([b[0]^1])+b[1:]
 if p==P/'proposals.json' and mode=='--negative-size':b+=b' '
 assert len(b)==e.get('size',e.get('bytes')),('SIZE',str(p))
 assert digest(b)==e['sha256'],('HASH',str(p))
def exact(root,m):
 entries=m['files'];names={e['path'] for e in entries};assert len(names)==len(entries)
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 if root==P and mode=='--negative-extra':actual.add('UNLISTED-NEGATIVE-FIXTURE')
 assert actual-set(m['excluded_exact_paths'])==names,('EXACT_PAYLOAD',str(root))
 for e in entries:
  assert not pathlib.Path(e['path']).is_absolute() and '..' not in pathlib.Path(e['path']).parts
  check(root/e['path'],e)
def main():
 m=j(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(P,m)
 refs=j(P/'flat-bindings.json');assert len({e['path'] for e in refs})==len(refs)
 for e in refs:check(pathlib.Path(e['path']),e)
 check(I/'manifest.json',{'size':10593,'sha256':'92a14f8ea8bb6f488dde4e6c692abcf8d3ec2dc922da7a7fdb30ea29cc6233c6'})
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json')
 for e in pairs:
  for k in ('original','copy'):check(pathlib.Path(e[k]),e)
  assert pathlib.Path(e['original']).read_bytes()==pathlib.Path(e['copy']).read_bytes()
 check(C/'manifest.json',{'size':22047,'sha256':'4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15'})
 inv=j(C/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4983
 active=j(I/'active-breadth-reservations.json');seen=set();protected=set()
 for a in active:
  ids=set(a['ids']);assert len(ids)==len(a['ids'])==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(a['protected_ids']);seen|=ids;protected|=set(a['protected_ids'])
 assert len(seen)==150 and not seen&protected
 for a in active:assert set(a['other_active_reservations'])==seen-set(a['ids'])
 res=j(I/'reserved-ids.json');ids=set(res['ids']);assert res['lane']==P.name and res['coverage_baseline']==4983 and len(ids)==50
 assert any(a['lane']==P.name and set(a['ids'])==ids for a in active)
 queue=j(I/'queue.json');assert len(queue)==50 and {q['mathdb_id'] for q in queue}==ids
 ds=j(P/'dispositions.json');assigned=j(P/'assigned-records.json');assert len(ds)==len(assigned)==50 and {d['mathdb_id'] for d in ds}=={d['mathdb_id'] for d in assigned}==ids
 assert len({d['mathdb_id'] for d in ds})==50
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),n,r)
 assert len(found)==50
 for collection in (ds,assigned):
  for d in collection:
   path,n,r=found[d['mathdb_id']];assert d['corpus_chunk']==path and d['corpus_line']==n and d['statement']==r['statement']
   assert d['statement_utf8_sha256']==digest(r['statement'].encode('utf-8'))
   assert d['canonical_record_sha256']==digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
   if collection is assigned:assert d['record']==r
   else:assert d['accepted_credit']==0 and d['current_registry_cleared'] is False and d['technical_reason']
 for q in queue:
  r=found[q['mathdb_id']][2]
  for k in ('canonical_url','title','post_type','statement_completeness'):assert q[k]==r[k]
 assert j(P/'proposals.json')==[]
 for s in j(P/'source-provenance.json'):
  if 'path' in s:
   check(pathlib.Path(s['path']),s);check(pathlib.Path(s['derivative']['path']),s['derivative'])
 result={'integrity':'PASS','mathematical_acceptance':False,'novelty_registry_clearance':False,'literal_statements':50,'baseline':4983,'proposals':0,'flat_references':len(refs),'original_copy_pairs':len(pairs),'original_chunks':20,'frozen_inputs':8,'active_reserved_ids':150,'exact_payload_files':len(m['files'])}
 print(json.dumps(result,sort_keys=True))
if __name__=='__main__':
 try:main()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
