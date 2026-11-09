"""Independent read-only byte, assignment and literal-record verifier. Never executes upstream code."""
import pathlib,json,hashlib,datetime,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r563';C=L/'pi-mathdb-full-corpus-inventory-r301'
def h(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_bytes())
def check_bytes(b,e):
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch')
 if h(b)!=e['sha256']:raise ValueError('hash mismatch')
def check(p,e):
 try:check_bytes(p.read_bytes(),e)
 except Exception as ex:raise ValueError(str(p)+': '+str(ex)) from ex
def names_check(actual,m):
 if actual-set(m['excluded_exact_paths'])!={e['path'] for e in m['files']}:raise ValueError('extra/missing payload file')
 if len(m['files'])!=len({e['path'] for e in m['files']}):raise ValueError('duplicate manifest path')
def exact(root,m):
 names_check({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()},m)
 for e in m['files']:check(root/e['path'],e)
def negatives():
 b=(P/'SUMMARY.md').read_bytes();e={'size':len(b),'sha256':h(b)};result={}
 for name,altered in [('size',b+b'\0'),('hash_same_size',bytes([b[0]^1])+b[1:])]:
  try:check_bytes(altered,e)
  except ValueError:result[name]='rejected'
  else:raise ValueError('negative accepted: '+name)
 m={'files':[{'path':'SUMMARY.md',**e}],'excluded_exact_paths':[]}
 try:names_check({'SUMMARY.md','unexpected'},m)
 except ValueError:result['extra_file']='rejected'
 else:raise ValueError('negative accepted: extra')
 return result
def verify():
 # Initial observations and all later flat references are checked independently.
 for line in (P/'initial-sha256.txt').read_text().splitlines():
  sha,path=line.split('  ',1)
  if h(pathlib.Path(path).read_bytes())!=sha:raise ValueError('initial hash '+path)
 for line in (P/'initial-sizes.txt').read_text().splitlines():
  size,path=line.split(' ',1)
  if pathlib.Path(path).stat().st_size!=int(size):raise ValueError('initial size '+path)
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json')
 for e in pairs:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json')
 if (C/'manifest.json').read_bytes()!=(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes():raise ValueError('inventory manifest mismatch')
 chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==5033
 active=j(I/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==150
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 res=j(I/'reserved-ids.json');ids=set(res['ids']);assert res['lane']==P.name and len(ids)==50
 assert ids=={r['mathdb_id'] for r in j(I/'queue.json')}
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 assert len(found)==50
 for d in ds:
  p,n,r=found[d['mathdb_id']];assert d['corpus_chunk']==str(p) and d['corpus_line']==n and d['literal_statement']==r['statement']
  assert d['statement_sha256']==h(r['statement'].encode('utf8'))
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf8'))
  assert d['accepted_credit']==0 and not d['current_registry_cleared'] and d['literal_bytes_read'] and d['technical_assessment']
 assert j(P/'proposals.json')==[]
 for e in j(P/'downloads.json'):
  if 'path' in e:check(pathlib.Path(e['path']),e)
 for e in j(P/'derivative-bindings.json'):check(pathlib.Path(e['path']),e)
 m=j(P/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'};exact(P,m)
 neg=negatives();assert j(P/'negative-test-results.json')==neg
 b=(P/'manifest.json').read_bytes()
 return {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','scientific_acceptance':False,'current_registry_cleared':False,'baseline':5033,'literal_records':50,'complete_mathematical_statements':49,'proposals':0,'accepted_credit':0,'original_chunks':20,'frozen_inputs':8,'binding_pairs':len(pairs),'reserved_disjoint':150,'payload_files':len(m['files']),'manifest_sha256':h(b),'manifest_size':len(b),'negative_rejections':neg}
if __name__=='__main__':
 try:print(json.dumps(verify(),indent=2))
 except Exception as ex:print(str(ex),file=sys.stderr);sys.exit(1)
