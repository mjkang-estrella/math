exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split('refs={};')[0])
f=json.loads((L/'input-bindings.json').read_text()); assert all(ref(e['path'])==e for e in f['refs'])
r=json.loads((R/'reserved-ids.json').read_text()); ids=set(r['ids']); old=json.loads((R/'coverage-delta.json').read_text()); assert len(ids)==50 and len(old)==1183 and not ids&set(map(int,old)) and not ids&set(r['other_active_reservations']) and not ids&{372627,372628,368940}
records=[]
for p in sorted((I/'corpus').glob('*.jsonl')):
 with p.open() as h:
  for line in h:
   x=json.loads(line)
   if x.get('mathdb_id',x.get('id')) in ids:records.append(x)
assert len(records)==50
(L/'records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(records[:1],ensure_ascii=False,indent=2));print('all extracted',len(records))
