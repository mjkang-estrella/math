exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split("A=L/")[0])
A=L/'root-mathdb-breadth-intake-r425';a=json.loads((A/'reserved-ids.json').read_text());ids=set(map(str,a['ids']));q=json.loads((A/'queue.json').read_text());base=json.loads((A/'coverage-delta.json').read_text())
assert len(ids)==50 and ids==set(str(x['mathdb_id']) for x in q) and len(base)==2033
assert not ids&(set(base)|set(map(str,a['other_active_reservations']))|set(map(str,[372627,372628,368940,404067,364119])))
found=[]
I=L/'pi-mathdb-full-corpus-inventory-r301'
for e in json.loads((I/'manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'):continue
 for line in (I/e['path']).open():
  x=json.loads(line)
  if str(x['mathdb_id']) in ids:found.append(x)
assert len(found)==50
found.sort(key=lambda x:a['ids'].index(x['mathdb_id']))
(R/'selected-records.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
with (R/'statements.txt').open('w') as f:
 for x in found:f.write('\nID '+str(x['mathdb_id'])+'\n'+x['statement']+'\n')
print('exact assignment/disjointness pass');print('record keys',list(found[0]));print((R/'statements.txt').read_text())
