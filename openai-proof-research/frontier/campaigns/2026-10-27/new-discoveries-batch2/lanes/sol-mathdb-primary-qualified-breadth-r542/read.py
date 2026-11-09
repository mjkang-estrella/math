exec(open(__file__.replace('read.py','bind.py')).read().split("for name in ['coverage-delta.json'")[0])
for p in (L/'root-mathdb-accepted-exclusions-r304').iterdir():
 if p.is_file():bind(p)
(O/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
s=J(I/'reserved-ids.json');groups=[set(x['ids']) for x in J(I/'active-breadth-reservations.json')];cov=set(map(int,J(I/'coverage-delta.json')));assert len(cov)==4483
for i,g in enumerate(groups):
 assert len(g)==50 and not g&cov and not g&set(s['protected_ids'])
 for h in groups[:i]:assert not g&h
assert set(s['ids'])=={x['mathdb_id'] for x in J(I/'queue.json')}
records=[]
for e in r['files']:
 if not e['path'].startswith('corpus/'):continue
 for n,line in enumerate((R/e['path']).open(),1):
  x=json.loads(line)
  if x['mathdb_id'] in s['ids']:records.append({'chunk':str(R/e['path']),'line':n,'record':x})
assert len(records)==50
(O/'assigned-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
print('record keys',records[0]['record'].keys())
for i,a in enumerate(records):
 print('\n===',i+1,a['record']['mathdb_id'],'===\n',json.dumps(a['record'],ensure_ascii=False))
