exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split('for p in T.iterdir():')[0])
ids=json.loads((T/'reserved-ids.json').read_text())['ids']; found={}
for e in json.loads((I/'manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'): continue
 with (I/e['path']).open() as f:
  for line in f:
   x=json.loads(line)
   if x['mathdb_id'] in ids: found[x['mathdb_id']]=x
assert set(found)==set(ids)
put('records.json',[found[n] for n in ids])
for n in ids:
 x=found[n];print('\nID',n,x.get('title'));print(x['statement']);print('SOURCE',json.dumps({k:v for k,v in x.items() if 'source' in k or 'reference' in k},ensure_ascii=False))
