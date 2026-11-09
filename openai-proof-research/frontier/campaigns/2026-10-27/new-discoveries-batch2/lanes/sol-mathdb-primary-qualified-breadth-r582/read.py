exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('out=[]')[0])
q=json.loads((I/'queue.json').read_text());s=json.loads((I/'reserved-ids.json').read_text());cov=json.loads((I/'coverage-delta.json').read_text());a=json.loads((I/'active-breadth-reservations.json').read_text());ids=set(s['ids']);assert len(q)==len(ids)==50 and ids=={x['mathdb_id'] for x in q};assert len(cov)==5483
sets=[set(x['ids']) for x in a];assert len(set.union(*sets))==sum(map(len,sets));assert all(not t&set(map(int,cov)) and not t&set(s['protected_ids']) for t in sets)
rows=[]
for p in sorted((R/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  x=json.loads(line)
  if x.get('id',x.get('mathdb_id')) in ids:rows.append({'corpus_chunk':str(p),'line':n,'record':x})
assert len(rows)==50
for x in rows:
 r=x['record'];print('RECORD',r.keys()) if len(rows)==0 else None
(D/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(rows[0],ensure_ascii=False,indent=2))
