exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('b={}')[0])
q=j(I/'queue-r612.json');ids={x['mathdb_id'] for x in q};res=j(I/'reserved-ids-r612.json');cov=j(I/'coverage-delta.json');ars=j(I/'active-breadth-reservations.json');adj=j(I/'adjudications.json')
assert ids==set(res['ids']) and len(ids)==50 and len(cov)==6233
sets=[set(x['ids']) for x in ars];assert any(x==ids for x in sets)
for n,s in enumerate(sets):
 assert not set(map(str,s))&set(cov)
 for t in sets[:n]:assert not s&t
print('DISJOINT', [len(s) for s in sets]);print('ADJ',json.dumps(adj));print('HYP', (I/'hypothesis-queue.json').read_text())
rows=[]
for e in j(C/'manifest.json')['files']:
 if not e['path'].startswith('corpus/'):continue
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:rows.append({'corpus_chunk':str(p),'corpus_line':n,'record':r})
assert len(rows)==50
(P/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for row in rows:
 r=row['record'];print('\nID',r['mathdb_id'],json.dumps(r,ensure_ascii=False))
