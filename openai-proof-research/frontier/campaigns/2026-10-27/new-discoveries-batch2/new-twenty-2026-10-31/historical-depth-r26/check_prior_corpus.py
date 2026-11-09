import json,pathlib,hashlib,resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(15,15));os.sched_setaffinity(0,{0,1})
D=pathlib.Path(__file__).resolve().parent;B=D.parent.parent;raw=json.loads((D/'raw-bindings.json').read_text());wanted={x['path']:x['chunk_sha256'] for x in raw.values()};receipts=[]
for n in ['sol-mathdb-primary-qualified-breadth-r390/corpus-bindings.json','sol-mathdb-primary-qualified-breadth-r392/input-bindings.json','sol-mathdb-primary-qualified-breadth-r394/input-bindings.json']:
 p=B/'lanes'/n;data=p.read_bytes();d=json.loads(data);refs=d.get('refs',d.get('references',[]));hits=[]
 for x in refs:
  if x.get('path') in wanted:
   assert x['sha256']==wanted[x['path']];hits.append(x)
 receipts.append(dict(binding_path=str(p),binding_sha256=hashlib.sha256(data).hexdigest(),matching_corpus_bindings=hits))
assert all(x['matching_corpus_bindings'] for x in receipts)
(D/'prior-corpus-comparison.json').write_text(json.dumps(receipts,indent=2));print('PASS prior corpus references for each of r390/r392/r394 match actual raw chunk hash')
