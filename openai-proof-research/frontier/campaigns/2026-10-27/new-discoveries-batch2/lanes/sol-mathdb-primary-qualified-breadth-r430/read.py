exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split('bind={};')[0])
ids=set(load(I/'reserved-ids.json')['ids']);out=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for line in p.open():
  d=json.loads(line)
  if d.get('id',d.get('mathdb_id')) in ids:out.append(d)
print('found',len(out));print(json.dumps(out[0],ensure_ascii=False,indent=2))
(O/'assigned-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for p in [I/'DECISION.md',L/'root-mathdb-cayley-review-intake-r363/disposition.json',L/'root-mathdb-accepted-exclusions-r304/README.md']:
 print(str(p),p.read_text()[:7500])
print('coverage keys',load(I/'coverage-delta.json').keys())
