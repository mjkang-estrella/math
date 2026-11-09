exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("print('VERIFIED'")[0])
ids=set(json.loads((I/'reserved-ids.json').read_text())['ids']); rows=[]
for chunk in sorted((R/'corpus').glob('*.jsonl')):
 for line,s in enumerate(chunk.open(),1):
  x=json.loads(s)
  if x.get('id',x.get('mathdb_id')) in ids:
   rows.append({'chunk':str(chunk),'line':line,'record':x})
(P/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('COUNT',len(rows));print(json.dumps(rows[0],ensure_ascii=False,indent=2))
