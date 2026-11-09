"""Independent read-only verifier. Run under the required fixed helper guard."""
import pathlib,json,hashlib,sys,itertools
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r571';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def validate_bytes(b,e):
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch')
 if h(b)!=e['sha256']:raise ValueError('hash mismatch')
def check(p,e):validate_bytes(p.read_bytes(),e)
def names_check(actual,expected):
 if actual!=expected:raise ValueError('extra/missing files: '+str(actual^expected))
def exact(root,m):
 names=[e['path'] for e in m['files']];assert len(names)==len(set(names));names_check({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()},set(names)|set(m['excluded_exact_paths']))
 for e in m['files']:check(root/e['path'],e)
def negatives():
 e={'size':3,'sha256':h(b'abc')};tests=[('hash',lambda:validate_bytes(b'abd',e)),('size',lambda:validate_bytes(b'abcd',e)),('extra',lambda:names_check({'a','extra'},{'a'}))];out={}
 for name,f in tests:
  try:f()
  except ValueError:out[name]='rejected';continue
  raise AssertionError('negative accepted '+name)
 return out

def main():
 exact(P,j(P/'manifest.json'))
 if '--manifest-sha' in sys.argv:assert h((P/'manifest.json').read_bytes())==sys.argv[sys.argv.index('--manifest-sha')+1]
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 assert h((I/'manifest.json').read_bytes())=='673835750099e45707372f880d12662ce9cc7ec2fc423863c262b819d55821fc';exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==5233;covered=set(map(int,cov));res=j(I/'reserved-ids.json');ids=set(res['ids']);assert len(ids)==50 and res['lane']==P.name;assert ids=={e['mathdb_id'] for e in j(I/'queue.json')}
 active=j(I/'active-breadth-reservations.json');sets=[set(e['ids']) for e in active];assert len(sets)==3 and all(len(s)==50 for s in sets)
 protected={337963,338290,339564,372627,372628,368940,404067,364119,366370,365437,365439};assert protected<=set(res['protected_ids'])
 for s in sets:assert not s&(covered|protected)
 for a,b in itertools.combinations(sets,2):assert not a&b
 assert set.union(*sets)-ids==set(res['other_active_reservations'])
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 assert set(found)==ids
 ds=j(P/'dispositions.json');ls=j(P/'literal-records.json');assert len(ds)==len(ls)==50 and {d['mathdb_id'] for d in ds}==ids and {d['mathdb_id'] for d in ls}==ids
 for d in ds+ls:
  p,n,r=found[d['mathdb_id']];assert d['chunk']==str(p) and d['line']==n and d['statement']==r['statement'];assert d['statement_utf8_sha256']==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  if 'record' in d:assert d['record']==r
 for d in ds:assert d['accepted_credit']==0 and not d['current_registry_cleared'] and d['literal_record_read']
 assert j(P/'proposals.json')==[]
 for name in ['source-provenance.json','derivative-bindings.json']:
  for e in j(P/name):
   if 'path' in e:check(P/e['path'],e)
 return {'integrity':'PASS','record_reviews':50,'primary_documents_selected_passages':7,'proposals':0,'corpus_chunks_checked_in_place':20,'separate_frozen_inputs_checked':8,'reservation_sets':3,'negative_tests':negatives(),'math_or_novelty_pass':False}
if __name__=='__main__':
 try:print(json.dumps(main(),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
