"""Independent, bounded, read-only integrity validation; never executes upstream code."""
import pathlib,json,hashlib,sys,datetime,collections
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r473';V=L/'pi-mathdb-full-corpus-inventory-r301'
def read(p):return json.loads(p.read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def check(p,e):
 assert p.is_file(),str(p)
 assert sha(p)==e['sha256'],('hash mismatch',str(p))
 assert p.stat().st_size==e.get('bytes',e.get('size',p.stat().st_size)),('size mismatch',str(p))
def canon(x):return hashlib.sha256(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()
refs=read(O/'bindings.json')['flat_refs'];assert len({e['path'] for e in refs})==len(refs)
for e in refs:check(pathlib.Path(e['path']),e)
for name in ['root-mathdb-breadth-intake-r473','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 base=L/name;m=read(base/'manifest.json')
 for e in (m if isinstance(m,list) else m['files']+m.get('frozen_inputs',[])):check(base/e['path'],e)
# Direct actual originals from intake, never recursive binding expansion.
for e in read(I/'bindings.json'):
 check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
m=read(V/'manifest.json');chunks=[e for e in m['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20;assert len(m['frozen_inputs'])==8
for e in chunks+m['frozen_inputs']:check(V/e['path'],e)
r=read(I/'reserved-ids.json');q=read(I/'queue.json');ids=r['ids'];assert len(ids)==len(set(ids))==50;assert r['lane']==O.name;assert ids==[e['mathdb_id'] for e in q]
assert not(set(ids)&set(r['other_active_reservations']));assert not(set(ids)&{372627,372628,368940,404067,364119});cov=read(I/'coverage-delta.json');assert len(cov)==3183;assert not(set(map(str,ids))&set(cov))
excluded=[]
def collect(x):
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ['mathdb_id','mathdb_ids','problem_ids','related_mathdb_id','mathdb_related_id']:excluded.extend(v if isinstance(v,list) else [v])
   else:collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
for fn in ['accepted-exclusions.json','historical-dispositions.json']:collect(read(L/'root-mathdb-accepted-exclusions-r304'/fn))
assert not(set(ids)&set(excluded))
s=read(O/'statements.json');d=read(O/'dispositions.json');assert len(s)==len(d)==50;assert set(ids)=={e['mathdb_id'] for e in d};assert len({e['mathdb_id'] for e in d})==50
orig={}
for e in chunks:
 p=V/e['path']
 for n,line in enumerate(p.open(),1):
  x=json.loads(line);i=x.get('mathdb_id',x.get('id'))
  if i in ids:
   assert i not in orig;orig[i]=(str(p),n,x)
assert len(orig)==50
for e in s+d:
 x=e['record'];i=x['mathdb_id'];p,n,y=orig[i];assert x==y;assert e['original_chunk']==p and e['original_line']==n;assert e['canonical_record_sha256']==canon(y)
 if 'literal_statement' in e:
  assert e['mathdb_id']==i;assert e['literal_statement']==y['statement'];assert e['statement_utf8_sha256']==hashlib.sha256(y['statement'].encode()).hexdigest();assert e['accepted_credit']==0;assert e['prior_cleared'] is False
for e in q:
 y=orig[e['mathdb_id']][2]
 for k in ['canonical_url','title','status','post_type','statement_completeness']:assert e[k]==y[k]
assert read(O/'proposals.json')==[]
for e in read(O/'retained-sources-final.json'):
 if 'path' in e:
  check(O/e['path'],e);p=O/'sources'/(e['arxiv']+'.txt');assert sha(p)==e['text_sha256'];assert e['url'].startswith('https://arxiv.org/pdf/');assert e['retrieved_utc']
# A separate arithmetic sanity check of the sharpness instance, not an all-vector theorem.
import itertools
vals=[abs(a+b) for a,b in itertools.product([-1,1],repeat=2)];assert sum(vals)==4 and sum(vals)**2==8*2
if '--preflight' not in sys.argv:
 m=read(O/'manifest.json');assert m['excluded_exact_relative_paths']==['manifest.json','final-receipt.json'];entries=m['files'];actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}-{'manifest.json','final-receipt.json'};assert actual=={e['path'] for e in entries};assert len(entries)==len(actual)
 for e in entries:check(O/e['path'],e)
result={'integrity':'PASS','math':'NOT_ESTABLISHED','novelty':'HOLD','assignment':50,'baseline_reported_reviews':3183,'inventory_chunks':20,'separately_listed_frozen_inputs':8,'proposals':0,'counts':'9 additional / 39 total / next 40','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
if '--receipt' in sys.argv:
 p=O/'final-receipt.json';assert not p.exists(),'never rewrite receipt';result['manifest_sha256']=sha(O/'manifest.json');p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
