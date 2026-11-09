exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split('# Administrative bindings')[0])
ids=set(load(I/'reserved-ids.json')['ids']); records=[]
for p in sorted((C/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for line,t in enumerate(p.open(),1):
  o=json.loads(t)
  if o.get('mathdb_id',o.get('id')) in ids:records.append({'chunk':str(p),'line':line,'record':o})
assert len(records)==50
(D/'assigned-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(records[0],ensure_ascii=False,indent=2))
