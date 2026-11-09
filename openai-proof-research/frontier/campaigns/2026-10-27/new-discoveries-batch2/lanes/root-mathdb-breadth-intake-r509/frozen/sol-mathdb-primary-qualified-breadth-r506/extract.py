from pathlib import Path
exec(Path(__file__).with_name('intake_check.py').read_text().split('binds=')[0])
R=L/'pi-mathdb-full-corpus-inventory-r301';r=load(R/'manifest.json');b=[]
for e in r['files']+r['frozen_inputs']:
 if e['path'].startswith('corpus/') or e in r['frozen_inputs']:
  v=h(R/e['path']);assert v['size']==e['bytes'] and v['sha256']==e['sha256'];b.append(v)
assert any(e['original']==str(R/'manifest.json') and e['sha256']==h(R/'manifest.json')['sha256'] for e in load(I/'bindings.json'))
write('corpus-bindings.json',b)
c=load(I/'coverage-delta.json');assert len(c)==3733
rs=load(I/'active-breadth-reservations.json');seen=set()
for q in rs:
 s=set(q['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,c)) and not s&set(q['protected_ids']);seen|=s
ids=set(load(I/'reserved-ids-r506.json')['ids']);assert ids=={e['mathdb_id'] for e in load(I/'queue-r506.json')}
out=[]
for e in r['files']:
 if not e['path'].startswith('corpus/'):continue
 for i,line in enumerate((R/e['path']).open(),1):
  x=json.loads(line)
  if x.get('mathdb_id',x.get('id')) in ids:
   out.append({'chunk':str(R/e['path']),'line':i,'record':x})
assert len(out)==50;write('assigned-records.json',out)
for j,x in enumerate(out):
 print('\nROW',j,x['line'],json.dumps(x['record'],ensure_ascii=False))
