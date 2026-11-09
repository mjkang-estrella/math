import json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent; I=B/'root-mathdb-breadth-intake-r415'; C=B/'pi-mathdb-full-corpus-inventory-r301'; H=B/'root-mathdb-history-bind-r304'
def load(p):return json.loads(p.read_text())
def ref(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
print('r304 dirs',[p.name for p in B.glob('*r304')])
h=next(B.glob('*r304'))
paths=[I/n for n in ['manifest.json','bindings.json','coverage-delta.json','queue.json','reserved-ids.json','queue-extension-bindings.json','routing-queue.jsonl']]+[C/'manifest.json',h/'manifest.json',h/'bindings.json',h/'accepted-exclusions.json',h/'historical-dispositions.json',B/'root-mathdb-cayley-review-intake-r363/disposition.json']
bind=load(I/'bindings.json')
for x in bind: paths.append(pathlib.Path(x['original']))
# Flat references only, no recursive dependency traversal.
m=load(C/'manifest.json');print('r301 manifest type',type(m).__name__)
files=m['files'] if isinstance(m,dict) else m
print('r301 paths',[x.get('path',x.get('file')) for x in files][:35])
for x in files:
 p=C/x['path']
 if 'chunk' in x['path'] and ('corpus/' in x['path']):paths.append(p)
refs=[ref(p) for p in dict.fromkeys(paths)]
(L/'bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':refs},indent=2)+'\n')
# Verify intake manifest without executing upstream verifier.
for x in load(I/'manifest.json')['files']:
 r=ref(I/x['path']);assert r['sha256']==x['sha256'] and r['size']==x['size'],x['path']
for x in bind:
 r=ref(pathlib.Path(x['original']));assert r['sha256']==x['sha256'] and r['size']==x['size'],x['original']
chunks=[]
for x in files:
 if 'chunk' in x['path'] and 'corpus/' in x['path']:
  r=ref(C/x['path']);assert r['sha256']==x['sha256'] and r['size']==x['bytes'];chunks.append(r)
assert len(chunks)==20,len(chunks)
(L/'freeze-check.json').write_text(json.dumps({'intake_manifest':'PASS','original_bindings':'PASS','r301_chunks':chunks},indent=2)+'\n')
print('FREEZE PASS',len(refs),len(chunks))
print('coverage keys',list(load(I/'coverage-delta.json')))
print('queue type',type(load(I/'queue.json')).__name__)
