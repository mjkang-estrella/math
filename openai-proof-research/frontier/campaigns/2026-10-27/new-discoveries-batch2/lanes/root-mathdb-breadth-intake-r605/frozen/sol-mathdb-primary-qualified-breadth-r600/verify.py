"""Independent read-only integrity checker. No imports/execution of upstream code."""
import pathlib,json,hashlib,sys,copy
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r599';R=L/'pi-mathdb-full-corpus-inventory-r301'
EX={'manifest.json','final-verification-receipt.json'}
def sha(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_text())
def checked(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}';assert sha(b)==e['sha256'],f'hash mismatch: {p}'
def payload(root,m,extra=False):
 entries=m['files'];names=[e['path'] for e in entries];assert len(names)==len(set(names))
 found={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 if extra:found.add('unexpected-negative-test')
 assert set(names)==found,'exact payload mismatch'
 for e in entries:
  assert not pathlib.Path(e['path']).is_absolute() and '..' not in pathlib.Path(e['path']).parts
  checked(root/e['path'],e)
def run():
 m=j(D/'manifest.json');assert set(m['excluded_exact_paths'])==EX
 neg=sys.argv[2] if len(sys.argv)>2 and sys.argv[1]=='--negative' else None
 if neg:
  m=copy.deepcopy(m)
  if neg=='hash':m['files'][0]['sha256']='0'*64
  elif neg=='size':m['files'][0]['size']+=1
  elif neg!='extra':raise ValueError('unknown negative')
  payload(D,m,neg=='extra');raise RuntimeError('negative incorrectly accepted')
 payload(D,m)
 bindings=j(D/'flat-bindings.json');assert len(bindings)==len({e['path'] for e in bindings})
 for e in bindings:checked(pathlib.Path(e['path']),e)
 payload(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ('original','copy'):checked(pathlib.Path(e[k]),e)
 inventory=j(R/'manifest.json');chunks=[e for e in inventory['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(inventory['frozen_inputs'])==8
 for e in chunks+inventory['frozen_inputs']:checked(R/e['path'],e)
 res=j(I/'reserved-ids.json');ids=set(res['ids']);assert len(ids)==50 and res['lane']==D.name
 assert ids=={e['mathdb_id'] for e in j(I/'queue.json')}
 cov=j(I/'coverage-delta.json');assert len(cov)==5933
 protected={337963,338290,339564,372627,372628,368940,404067,364119,366370,365437,365439};used=set(map(int,cov))|protected;selfcount=0
 for a in j(I/'active-breadth-reservations.json'):
  s=set(a['ids']);assert len(s)==50
  if a['lane']==D.name:assert s==ids;selfcount+=1;continue
  assert not used&s;used|=s
 assert selfcount==1 and not used&ids
 actual={}
 for e in chunks:
  p=R/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in actual;actual[r['mathdb_id']]=(r,str(p),n)
 lit=j(D/'literal-records.json');disp=j(D/'dispositions.json');assert len(lit)==len(disp)==50
 assert {e['mathdb_id'] for e in lit}=={e['mathdb_id'] for e in disp}==ids
 for e in lit:
  r,p,n=actual[e['mathdb_id']];assert e['record']==r and e['corpus_path']==p and e['line']==n
  assert sha(r['statement'].encode('utf-8'))==e['statement_utf8_sha256']
  assert sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))==e['canonical_record_sha256']
  d=next(x for x in disp if x['mathdb_id']==e['mathdb_id'])
  assert d['statement']==r['statement'] and d['statement_utf8_sha256']==e['statement_utf8_sha256'] and d['canonical_record_sha256']==e['canonical_record_sha256'] and d['corpus_line']==n and d['corpus_path']==p
  assert d['scope_flags']['literal_statement_read'] and not d['scope_flags']['current_registry_cleared'] and d['accepted_credit']==0
 assert j(D/'proposals.json')==[]
 for e in j(D/'source-provenance.json'):
  if 'path' in e:checked(pathlib.Path(e['path']),e)
 for e in j(D/'derivative-bindings.json'):checked(pathlib.Path(e['path']),e)
 print(json.dumps({'integrity':'PASS','mathematics_or_novelty_pass':False,'literal_record_reviews':50,'proposals':0,'baseline_record_reviews':5933,'original_chunks':20,'frozen_inputs':8,'direct_pairs':len(j(I/'bindings.json')),'flat_bindings':len(bindings),'manifest_sha256':sha((D/'manifest.json').read_bytes()),'manifest_size':(D/'manifest.json').stat().st_size}))
if __name__=='__main__':
 try:run()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
