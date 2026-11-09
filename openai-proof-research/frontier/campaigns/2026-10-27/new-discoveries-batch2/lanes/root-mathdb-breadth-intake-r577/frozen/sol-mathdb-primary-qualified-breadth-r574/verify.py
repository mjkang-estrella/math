#!/usr/bin/env python3
"""Independent read-only verifier. Run through the assigned fixed helper guard."""
import sys,json,pathlib,hashlib,itertools
P=pathlib.Path(__file__).resolve().parent
EX={'manifest.json','final-verification-receipt.json'}
def j(p):return json.loads(p.read_text())
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')), 'size mismatch '+str(p)
 assert hashlib.sha256(b).hexdigest()==e['sha256'],'hash mismatch '+str(p)
def payload(p):
 m=j(p/'manifest.json');assert set(m['excluded_exact_paths'])==EX
 paths=[e['path'] for e in m['files']];assert len(paths)==len(set(paths))
 assert all(not pathlib.Path(x).is_absolute() and '..' not in pathlib.Path(x).parts for x in paths)
 actual={str(x.relative_to(p)) for x in p.rglob('*') if x.is_file()};assert actual==set(paths)|(actual&EX),'extra/missing payload'
 for e in m['files']:check(p/e['path'],e)
def main():
 if len(sys.argv)==3 and sys.argv[1]=='--fixture':payload(pathlib.Path(sys.argv[2]));print('fixture PASS');return
 payload(P)
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 L=P.parent;I=L/'root-mathdb-breadth-intake-r573';C=L/'pi-mathdb-full-corpus-inventory-r301'
 assert hashlib.sha256((I/'manifest.json').read_bytes()).hexdigest()=='322fe68829f8f42be94f48241a0d289e77e9d9aa900daf0d08ac3da4dbf75caf'
 im=j(I/'manifest.json');actual={str(x.relative_to(I)) for x in I.rglob('*') if x.is_file()};assert actual=={e['path'] for e in im['files']}|set(im['excluded_exact_paths'])
 for e in im['files']:check(I/e['path'],e)
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 r=j(I/'reserved-ids.json');ids=set(r['ids']);assert len(ids)==50
 cov=j(I/'coverage-delta.json');assert len(cov)==5283
 reservations=j(I/'active-breadth-reservations.json');assert len(reservations)==3
 sets=[set(x['ids']) for x in reservations];assert [x['lane'] for x in reservations].count(P.name)==1
 assert next(set(x['ids']) for x in reservations if x['lane']==P.name)==ids
 for a in sets:assert len(a)==50 and not a&set(map(int,cov)) and not a&set(r['protected_ids'])
 for a,b in itertools.combinations(sets,2):assert not a&b
 assert set().union(*(set(x['ids']) for x in reservations if x['lane']!=P.name))==set(r['other_active_reservations'])
 assert {x['mathdb_id'] for x in j(I/'queue.json')}==ids
 original={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   v=json.loads(line)
   if v['mathdb_id'] in ids:
    assert v['mathdb_id'] not in original
    original[v['mathdb_id']]=(v,str(p),n)
 assigned=j(P/'assigned-records.json');ds=j(P/'dispositions.json');assert len(assigned)==len(ds)==50
 assert {x['record']['mathdb_id'] for x in assigned}=={x['mathdb_id'] for x in ds}==ids
 for x in assigned:
  v,path,line=original[x['record']['mathdb_id']];assert x['record']==v and x['chunk']==path and x['line']==line
  can=hashlib.sha256(json.dumps(v,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest();st=hashlib.sha256(v['statement'].encode()).hexdigest()
  assert x['canonical_record_sha256']==can and x['statement_utf8_sha256']==st
  d=next(d for d in ds if d['mathdb_id']==v['mathdb_id'])
  assert d['statement']==v['statement'] and d['canonical_record_sha256']==can and d['statement_utf8_sha256']==st
  assert d['corpus_chunk']==path and d['corpus_line']==line and d['accepted_credit']==0
 assert len(j(P/'proposals.json'))<=3 and j(P/'proposals.json')==[]
 for e in j(P/'source-provenance.json')+j(P/'derivative-bindings.json'):
  if 'path' in e:check(pathlib.Path(e['path']),e)
 neg=j(P/'negative-test-results.json');assert all(neg[k]['exit_code']!=0 for k in ['hash','size','extra']) and neg['control']['exit_code']==0
 print(json.dumps({'integrity':'PASS','literal_record_reviews':50,'proposals':0,'baseline_record_reviews':5283,'original_chunks':20,'frozen_inputs':8,'original_copy_pairs':41,'flat_bindings':len(j(P/'flat-bindings.json')),'reservation_disjointness':True,'payload_exact':True,'mathematical_acceptance':False,'novelty_cleared':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
