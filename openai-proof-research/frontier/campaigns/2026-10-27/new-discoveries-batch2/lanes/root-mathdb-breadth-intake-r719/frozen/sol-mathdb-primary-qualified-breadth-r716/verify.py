"""Independent read-only verifier. Run only through the assigned fixed helper guard."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r715';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def check_bytes(b,e):
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch')
 if sha(b)!=e['sha256']:raise ValueError('hash mismatch')
def check(p,e):
 try:check_bytes(p.read_bytes(),e)
 except Exception as ex:raise ValueError(str(p)+': '+str(ex)) from ex

def names_check(actual,expected):
 if actual!=expected:raise ValueError('exact payload mismatch: '+str(actual^expected))
def exact(root,m):
 es=m['files'];names={e['path'] for e in es};assert len(es)==len(names)
 names_check({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']),names)
 for e in es:check(root/e['path'],e)
def validate():
 # Own payload includes this verifier and every helper; no recursive upstream verification.
 m=j(P/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'};exact(P,m)
 refs=j(P/'flat-bindings.json')
 for e in refs:check(pathlib.Path(e['path']),e)
 assert str(I/'verification-receipt.json') in {e['path'] for e in refs}
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json')
 for e in pairs:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 assert (C/'manifest.json').read_bytes()==(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==8783
 active=j(I/'active-breadth-reservations.json');assert len(active)==3;seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==150
 assert any(r['lane'].endswith('r628') and r['status']=='rate_limit_held_not_reconciled' for r in active)
 assert any(r['lane'].endswith('r714') for r in active)
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 res=j(I/'reserved-ids-r716.json');ids=set(res['ids']);assert res['coverage_baseline']==8783 and len(ids)==50 and not ids&set(res['protected_ids'])
 assert ids=={r['mathdb_id'] for r in j(I/'queue-r716.json')}
 assert ids==set(next(r for r in active if r['lane']==P.name)['ids'])
 ds=j(P/'dispositions.json');ls=j(P/'literal-records.json');assert len(ds)==len(ls)==50 and {d['mathdb_id'] for d in ds}==ids and {d['mathdb_id'] for d in ls}==ids
 found={}
 for e in chunks:
  for n,line in enumerate((C/e['path']).open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(e['path'],n,r)
 assert set(found)==ids
 for d in ds:
  ck,n,r=found[d['mathdb_id']];assert d['corpus_chunk']==ck and d['corpus_line']==n
  assert d['exact_utf8_statement']==r['statement'] and d['statement_utf8_sha256']==sha(r['statement'].encode())
  assert d['canonical_record_sha256']==sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert d['classification'] in {'complete','definition-dependent','scope-ambiguous','incomplete'} and d['complete_self_contained_statement']==(d['classification']=='complete')
  assert d['classification_reason_and_quantifiers'] and d['accepted_credit']==0 and d['prior_cleared'] is False
 for d in ls:assert (d['corpus_chunk'],d['corpus_line'],d['record'])==found[d['mathdb_id']]
 assert j(P/'proposals.json')==[]
 for s in j(P/'source-provenance.json'):
  for k in ['abs_binding','pdf_binding','text_binding']:
   if k in s:check(pathlib.Path(s[k]['path']),s[k])
 calc=j(P/'calculations.json');assert calc['gaussian']['sum']==[1,0]
 assert len(calc['generator_exception_witnesses'])==20
 for w in calc['generator_exception_witnesses']:
  p=w['p'];g=w['g'];assert next(t for t in range(1,p) if pow(g,t,p)==1)==p-1
  assert (g*g+4)%p==w['value'] and pow(w['value'],(p-1)//2,p)==p-1
 # Bounded negatives use virtual mutations of actual bound bytes/names. Originals never altered.
 b=(P/'SUMMARY.md').read_bytes();e={'size':len(b),'sha256':sha(b)};negative=[]
 for kind,fn in [('hash',lambda:check_bytes(bytes([b[0]^1])+b[1:],e)),('size',lambda:check_bytes(b+b'X',e)),('extra-file',lambda:names_check({x['path'] for x in m['files']}|{'UNEXPECTED'}, {x['path'] for x in m['files']}))]:
  try:fn()
  except ValueError:negative.append(kind)
  else:raise AssertionError('negative accepted '+kind)
 return {'integrity':'PASS','literal_records':50,'baseline':8783,'original_chunks':20,'frozen_inputs':8,'original_copy_pairs':len(pairs),'flat_bindings':len(refs),'reserved_ids':150,'disjoint':True,'negative_rejections':negative,'negative_method':'virtual hash/size/payload mutations through same validators, originals unchanged','proposals':0,'credit':0,'scientific_novelty_acceptance':False,'manifest':{'sha256':sha((P/'manifest.json').read_bytes()),'size':(P/'manifest.json').stat().st_size}}
if __name__=='__main__':
 try:print(json.dumps(validate(),sort_keys=True))
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
