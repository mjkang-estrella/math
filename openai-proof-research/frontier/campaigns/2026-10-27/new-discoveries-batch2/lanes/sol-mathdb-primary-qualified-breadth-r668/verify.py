import pathlib,json,hashlib,sys
O=pathlib.Path(__file__).resolve().parent
EX={'manifest.json','final-verification-receipt.json'}
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),('size',str(p));assert digest(b)==e['sha256'],('hash',str(p))
def payload(m,extra=False):
 actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}-EX
 if extra:actual.add('unlisted-negative-probe')
 assert actual=={e['path'] for e in m['files']},'extra or missing payload'
 for e in m['files']:check(O/e['path'],e)
def main():
 m=load(O/'manifest.json');assert set(m['excluded_exact_paths'])==EX;payload(m)
 for e in load(O/'initial-bindings.json'):check(pathlib.Path(e['path']),e)
 L=O.parent;I=L/'root-mathdb-breadth-intake-r667';im=load(I/'manifest.json')
 assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in im['files']}|set(im['excluded_exact_paths'])
 for e in im['files']:check(I/e['path'],e)
 for e in load(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 R=L/'pi-mathdb-full-corpus-inventory-r301';rm=load(R/'manifest.json');chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for e in chunks+rm['frozen_inputs']:check(R/e['path'],e)
 res=load(I/'reserved-ids-r668.json');ids=set(res['ids']);q=load(I/'queue-r668.json');assert len(ids)==50 and ids=={x['mathdb_id'] for x in q}
 coverage=load(I/'coverage-delta.json');assert len(coverage)==7583
 sets=[set(x['ids']) for x in load(I/'active-breadth-reservations.json')]
 for j,s in enumerate(sets):
  assert not s&set(map(int,coverage));assert not s&set(res['protected_ids'])
  for t in sets[j+1:]:assert not s&t
 lit=load(O/'literal-records.json');ds=load(O/'dispositions.json');assert len(lit)==len(ds)==50;assert {x['mathdb_id'] for x in lit}=={x['mathdb_id'] for x in ds}==ids
 index={x['mathdb_id']:x for x in lit};found=set()
 for e in chunks:
  p=R/e['path']
  for line,b in enumerate(p.open('rb'),1):
   r=json.loads(b);i=r.get('mathdb_id',r.get('id'))
   if i not in ids:continue
   x=index[i];assert x['record']==r and x['chunk']==str(p) and x['line']==line;assert x['literal_line_sha256']==digest(b);assert x['canonical_record_sha256']==digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());found.add(i)
 assert found==ids
 for d in ds:
  x=index[d['mathdb_id']];assert d['statement']==x['record']['statement'];assert d['canonical_record_sha256']==x['canonical_record_sha256'];assert d['statement_sha256']==digest(d['statement'].encode());assert d['completeness'] in ['complete','definition-dependent','scope-ambiguous','incomplete'];assert d['completeness_reason'] and d['technical_assessment'];assert d['chunk']==x['chunk'] and d['line']==x['line']
 assert len(load(O/'proposals.json'))<=3
 for s in load(O/'source-provenance.json'):
  if 'sha256' in s:check(O/(s['name']+'.pdf'),s);check(pathlib.Path(s['derivative']['path']),s['derivative'])
 negatives={}
 for kind in ['hash','size','extra']:
  n=json.loads(json.dumps(m))
  if kind=='hash':n['files'][0]['sha256']='0'*64
  if kind=='size':n['files'][0]['size']+=1
  try:payload(n,kind=='extra')
  except AssertionError:negatives[kind]='rejected'
  else:raise AssertionError('negative accepted '+kind)
 receipt=O/'final-verification-receipt.json'
 if receipt.exists():
  f=load(receipt);check(O/'manifest.json',f['manifest'])
 print(json.dumps(dict(integrity='PASS',mathematics='NOT_CERTIFIED',novelty='HOLD',records=50,chunks=20,frozen_inputs=8,baseline=7583,negative_tests=negatives)))
if __name__=='__main__':main()
