import json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent; R=B.parents[4]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def put(n,x): (L/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
bind={}
def freeze(p,expected=None,size=None):
 p=pathlib.Path(p).resolve(); h=sha(p); n=p.stat().st_size
 if expected: assert h==expected,(str(p),'hash')
 if size is not None: assert n==size,(str(p),'bytes')
 bind[str(p)]={'path':str(p),'sha256':h,'bytes':n}
 return p
# Validate complete declared manifests and actual flat original/copy bindings, never execute upstream.
for name in ['root-mathdb-breadth-intake-r463','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=B/name; m=load(freeze(d/'manifest.json')); entries=m if isinstance(m,list) else m['files']
 for e in entries: freeze(d/e['path'],e['sha256'],e.get('size',e.get('bytes')))
 bp=d/'bindings.json'
 for e in load(bp):
  freeze(e['original'],e['sha256'],e.get('size',e.get('bytes')))
  if 'copy' in e: freeze(d/e['copy'],e['sha256'],e.get('size',e.get('bytes')))
I=B/'pi-mathdb-full-corpus-inventory-r301'; m=load(freeze(I/'manifest.json'))
chunks=[e for e in m['files'] if e['path'].startswith('corpus/')]; assert len(chunks)==20
frozen=[e for e in m['files'] if e['path'].startswith('frozen/')]
for e in chunks+frozen: freeze(I/e['path'],e['sha256'],e.get('bytes',e.get('size')))
put('inventory-frozen-membership.json',frozen)
# Freeze administrative history before interpretation.
for p in [B.parent/'ledger.json', B.parent/'prior-campaign-context.json']: pass
C=B.parent
for p in [C/'ledger.json',C/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md']:
 if p.exists(): freeze(p)
put('bindings.json',list(bind.values()))
T=B/'root-mathdb-breadth-intake-r463'; reservation=load(T/'reserved-ids.json'); ids=reservation['ids']; queue=load(T/'queue.json'); coverage=load(T/'coverage-delta.json')
assert len(ids)==len(set(ids))==50 and ids==[x['mathdb_id'] for x in queue]
assert reservation['lane']==L.name
assert len(coverage)==2983
assert not set(ids)&set(map(int,coverage))
assert not set(ids)&set(reservation['other_active_reservations'])
assert not set(ids)&{372627,372628,368940,404067,364119}
def assoc(x):
 out=set()
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ['mathdb_id','problem_id'] and isinstance(v,int): out.add(v)
   elif k in ['mathdb_ids','problem_ids'] and isinstance(v,list): out.update(a for a in v if isinstance(a,int))
   else: out.update(assoc(v))
 elif isinstance(x,list):
  for v in x: out.update(assoc(v))
 return out
ex=assoc(load(B/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json'))|assoc(load(B/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json'))
assert not set(ids)&ex
records=[]
for e in chunks:
 p=I/e['path']
 for line_no,line in enumerate(p.open(),1):
  rec=json.loads(line)
  if rec['mathdb_id'] in ids:
   assert not rec.get('historical'); records.append({'record':rec,'original_chunk':str(p),'original_line':line_no,'statement_utf8_sha256':hashlib.sha256(rec['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(rec,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()})
assert len(records)==50 and {x['record']['mathdb_id'] for x in records}==set(ids)
records.sort(key=lambda x:ids.index(x['record']['mathdb_id']))
put('records.json',records)
put('preflight.json',{'integrity':'PASS','chunks':20,'baseline_reported_reviews':len(coverage),'ids':ids,'excluded_associations':sorted(ex),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'upstream_code_executed':False})
with (L/'statements.txt').open('w') as f:
 for x in records:
  r=x['record']; f.write(f"\nID {r['mathdb_id']}: {r['title']}\nSOURCE {r['source_url']}\n{r['statement']}\n")
print('PASS: 50 exact assigned records, 20 chunks, flat manifests/originals, disjointness; statements ready')
