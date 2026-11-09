import json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parent.parent; O=pathlib.Path(__file__).resolve().parent; I=L/'root-mathdb-breadth-intake-r515'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def info(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def dump(n,x):(O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
paths=list(I.rglob('*')); paths=[p for p in paths if p.is_file()]
paths += [L.parent/'ledger.json',L.parent/'prior-campaign-context.json']
paths += list((L/'root-mathdb-accepted-exclusions-r304').glob('*.json'))
paths += list((L/'root-cayley-adjudication-r363').glob('*'))
paths=[p for p in paths if p.is_file()]
# Binding precedes any payload interpretation by this program.
bound={str(p):info(p) for p in paths};dump('flat-bindings.json',list(bound.values()))
m=json.loads((I/'manifest.json').read_text()); expected={x['path']:x for x in m['files']}
assert set(expected)=={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
for n,x in expected.items():
 a=info(I/n);assert a['sha256']==x['sha256'] and a['size']==x['size'],n
for x in json.loads((I/'bindings.json').read_text()):
 for key in ('original','copy'):
  p=pathlib.Path(x[key]);a=info(p);assert a['sha256']==x['sha256'] and a['size']==x['size'],str(p);bound[str(p)]=a
inv=json.loads((R/'manifest.json').read_text());assert str(R/'manifest.json') in bound
chunks=[x for x in inv['files'] if x['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20
assert len(inv['frozen_inputs'])==8
for x in chunks+inv['frozen_inputs']:
 p=R/x['path'];a=info(p);assert a['sha256']==x['sha256'] and a['size']==x['bytes'];bound[str(p)]=a
# More required original context, with binding before content read.
for p in L.glob('*363*/*'):
 if p.is_file():bound[str(p)]=info(p)
dump('flat-bindings.json',list(bound.values()))
r=json.loads((I/'reserved-ids.json').read_text());q=json.loads((I/'queue.json').read_text());c=json.loads((I/'coverage-delta.json').read_text());active=json.loads((I/'active-breadth-reservations.json').read_text())
sets=[set(x['ids']) for x in active];assert len(c)==3933
for i,s in enumerate(sets):
 assert not s&set(map(int,c));assert not s&set(r['protected_ids'])
 for t in sets[i+1:]:assert not s&t
assert set(r['ids'])=={x['mathdb_id'] for x in q};assert len(q)==50
assert not set(r['ids'])&(set(map(int,c))|set(r['other_active_reservations'])|set(r['protected_ids']))
wanted=set(r['ids']);out=[]
for x in chunks:
 p=R/x['path']
 for line,raw in enumerate(p.open(),1):
  rec=json.loads(raw);rid=rec.get('mathdb_id',rec.get('id'))
  if rid in wanted:out.append({'mathdb_id':rid,'chunk':str(p),'line':line,'record':rec,'canonical_record_sha256':hashlib.sha256(json.dumps(rec,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
dump('records.json',out)
dump('intake-verification.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS_INTEGRITY_ONLY','intake_manifest':info(I/'manifest.json'),'chunks':20,'frozen_inputs':8,'baseline':3933,'assigned':50,'binding_count':len(bound),'no_upstream_code_executed':True})
print(json.dumps({'records':len(out),'sample_record_keys':list(out[0]['record']),'bound':len(bound)}))
