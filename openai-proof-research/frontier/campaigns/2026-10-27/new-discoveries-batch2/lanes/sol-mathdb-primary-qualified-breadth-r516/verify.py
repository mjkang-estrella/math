#!/usr/bin/env python3
"""Independent read-only verifier. Run through the fixed helper_guard, python3 -B."""
import json,hashlib,pathlib,sys,itertools
O=pathlib.Path(__file__).resolve().parent
EX={'manifest.json','final-verification-receipt.json'}
def digest(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def check(p,x):
 b=p.read_bytes();assert len(b)==x.get('size',x.get('bytes')),('size',str(p));assert digest(b)==x['sha256'],('hash',str(p))
def payload(root):
 m=read(root/'manifest.json');assert set(m['excluded_exact_paths'])==EX
 expected={x['path']:x for x in m['files']};assert len(expected)==len(m['files'])
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-EX
 assert actual==set(expected),('exact_payload',sorted(actual-set(expected)),sorted(set(expected)-actual))
 for n,x in expected.items():
  assert not pathlib.Path(n).is_absolute() and '..' not in pathlib.Path(n).parts
  check(root/n,x)
 return len(expected)
def main():
 n=payload(O);bindings=read(O/'flat-bindings.json');bound={x['path']:x for x in bindings};assert len(bound)==len(bindings)
 for x in bindings:check(pathlib.Path(x['path']),x)
 I=O.parent/'root-mathdb-breadth-intake-r515';R=O.parent/'pi-mathdb-full-corpus-inventory-r301'
 im=read(I/'manifest.json');assert str(I/'manifest.json') in bound
 ie={x['path']:x for x in im['files']};ia={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(im['excluded_exact_paths']);assert set(ie)==ia
 for name,x in ie.items():check(I/name,x)
 for pair in read(I/'bindings.json'):
  for key in ['original','copy']:check(pathlib.Path(pair[key]),pair)
 check(R/'manifest.json',bound[str(R/'manifest.json')]); inv=read(R/'manifest.json');chunks=[x for x in inv['files'] if x['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for x in chunks+inv['frozen_inputs']:check(R/x['path'],x)
 reserved=read(I/'reserved-ids.json');q=read(I/'queue.json');covered=set(map(int,read(I/'coverage-delta.json')));assert len(covered)==3933
 assigned=set(reserved['ids']);assert len(assigned)==50 and assigned=={x['mathdb_id'] for x in q}
 assert not assigned&(covered|set(reserved['other_active_reservations'])|set(reserved['protected_ids']))
 sets=[set(x['ids']) for x in read(I/'active-breadth-reservations.json')]
 for s in sets:assert not s&(covered|set(reserved['protected_ids']))
 for s,t in itertools.combinations(sets,2):assert not s&t
 assert assigned in sets
 rows=read(O/'dispositions.json');st=read(O/'statements.json');rr=read(O/'records.json')
 assert len(rows)==len(st)==len(rr)==50 and {x['mathdb_id'] for x in rows}==assigned
 original={}
 for x in chunks:
  for line,raw in enumerate((R/x['path']).open(),1):
   rec=json.loads(raw)
   if rec['mathdb_id'] in assigned:original[rec['mathdb_id']]=(str(R/x['path']),line,rec)
 assert len(original)==50
 for collection in [rows,st,rr]:
  assert len({x['mathdb_id'] for x in collection})==50
  for x in collection:
   chunk,line,rec=original[x['mathdb_id']];assert x['chunk']==chunk and x['line']==line
   assert x['canonical_record_sha256']==digest(json.dumps(rec,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
   if 'record' in x:assert x['record']==rec
   else:
    s=rec['statement'];assert x['statement']==s and x['statement_sha256']==digest(s.encode()) and x['statement_utf8_size']==len(s.encode())
 for x in rows:assert x['literal_statement_read'] is True and x['accepted_credit']==0
 assert len(read(O/'proposals.json'))<=3
 for e in read(O/'source-provenance.json'):
  for key in ['pdf','text']:check(pathlib.Path(e[key]['path']),e[key])
 print(json.dumps({'status':'PASS_INTEGRITY_ONLY','payload_files':n,'original_chunks':20,'original_frozen_inputs':8,'baseline':3933,'literal_reviews':50,'proposals':len(read(O/'proposals.json')),'manifest_sha256':digest((O/'manifest.json').read_bytes()),'manifest_size':(O/'manifest.json').stat().st_size}))
if __name__=='__main__':
 try:
  if len(sys.argv)==3 and sys.argv[1]=='--payload-root':payload(pathlib.Path(sys.argv[2]));print('PASS_PAYLOAD_ONLY')
  else:main()
 except Exception as e:print('FAIL',repr(e),file=sys.stderr);sys.exit(1)
