exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split('manifest(I)')[0])
bindings=json.loads((R/'bindings.json').read_text())
for e in bindings['references']:bind(e['path'],e['role'],e)
res=json.loads((I/'reserved-ids.json').read_text()); ids=set(map(str,res['ids']))
old=json.loads((I/'coverage-delta.json').read_text())
assert len(ids)==50 and len(old)==1683 and not ids&set(old) and not ids&{'372627','372628','368940'}
assert not ids&set(map(str,res['other_active_reservations']))
rows=[];C=L/'pi-mathdb-full-corpus-inventory-r301'
for e in json.loads((C/'manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'):continue
 with (C/e['path']).open() as f:
  for line in f:
   x=json.loads(line)
   if str(x['mathdb_id']) in ids:
    rows.append(x)
assert len(rows)==50 and {str(x['mathdb_id']) for x in rows}==ids
(R/'records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(R/'assignment-check.json').write_text(json.dumps({'reserved':50,'reviewed_excluded':len(old),'other_reserved_disjoint':True,'special_exclusions_disjoint':True,'exactset':True},indent=2)+'\n')
for x in rows:
 print('\nID',x['mathdb_id']);print(json.dumps(x,ensure_ascii=False))
