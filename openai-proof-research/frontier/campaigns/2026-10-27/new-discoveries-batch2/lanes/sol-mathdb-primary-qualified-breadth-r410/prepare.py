exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split('paths=list')[0])
refs=[]
for x in json.loads((I/'bindings.json').read_text()):
 p=Path(x['original']);r=ref(p); assert r['sha256']==x['sha256'] and r['size']==x['size'];refs.append(r)
for p in B.glob('*r304/*'):
 if p.is_file():refs.append(ref(p))
C=B/'pi-mathdb-full-corpus-inventory-r301'
chunks=[x for x in json.loads((C/'manifest.json').read_text())['files'] if x['path'].startswith('corpus/')]
assert len(chunks)==20
for x in chunks:
 r=ref(C/x['path']);assert r['sha256']==x['sha256'] and r['size']==x['bytes'];refs.append(r)
(L/'bindings-originals.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'refs':refs},indent=2)+'\n')
# Read-only root manifest check. Do NOT invoke upstream verifier.
m=json.loads((I/'manifest.json').read_text())
for x in m['files']:
 r=ref(I/x['path']);assert r['sha256']==x['sha256'] and r['size']==x['size']
print('verified intake payload',len(m['files']),'originals',len(refs)-20,'chunks',len(chunks))
for name in ['reserved-ids.json','coverage-delta.json','queue.json']:
 d=json.loads((I/name).read_text());print(name,'type',type(d).__name__,'keys',list(d)[:12] if isinstance(d,dict) else 'list length '+str(len(d)))
 if name=='reserved-ids.json':print(json.dumps(d))
print('queue first',json.dumps(json.loads((I/'queue.json').read_text())[0])[:1500] if isinstance(json.loads((I/'queue.json').read_text()),list) else '')
