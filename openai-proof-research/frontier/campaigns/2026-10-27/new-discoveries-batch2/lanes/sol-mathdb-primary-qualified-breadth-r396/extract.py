exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split('paths=set()')[0])
ids=set(json.loads((I/'reserved-ids.json').read_text())['ids']);rows=[]
for e in json.loads((C/'manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'):continue
 check(C/e['path'],e)
 with (C/e['path']).open() as f:
  for line in f:
   x=json.loads(line)
   if x['mathdb_id'] in ids:rows.append(x)
assert len(rows)==50
rows.sort(key=lambda x:x['mathdb_id'])
(R/'records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for x in rows:print(json.dumps(x,ensure_ascii=False))
