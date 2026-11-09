exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("cm=load")[0])
q=load(I/'queue-r622.json'); ids={x['mathdb_id'] for x in q}; out=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('id',r.get('mathdb_id')) in ids:
   out.append({'chunk':str(p),'line':n,'record':r,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
(P/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print('RECORD KEYS',out[0]['record'].keys())
for x in out:print(json.dumps(x,ensure_ascii=False))
print('ACTIVE', (I/'active-breadth-reservations.json').read_text());print('FOCUSED',(I/'focused-assignment.json').read_text());print('ADJ',(I/'adjudications.json').read_text());print('HYP',(I/'hypothesis-queue.json').read_text())
