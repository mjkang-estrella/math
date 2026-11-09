exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("rows={}")[0])
r=J(I/'reserved-ids.json'); ids=set(r['ids']); cov=J(I/'coverage-delta.json');assert len(cov)==5433 and not ids&set(map(int,cov))
reserv=J(I/'active-breadth-reservations.json');seen=set()
for a in reserv:
 s=set(a['ids']);assert len(s)==50 and not seen&s and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
assert ids<=seen and not ids&set(r['other_active_reservations'])
print('RESERVATIONS',[(a['lane'],len(a['ids'])) for a in reserv])
out=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  a=json.loads(line)
  if int(a.get('id',a.get('mathdb_id',-1))) in ids:
   out.append(dict(id=int(a.get('id',a.get('mathdb_id'))),chunk=str(p),line=n,record=a,canonical_record_sha256=hashlib.sha256(json.dumps(a,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
assert len(out)==50
(D/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print('KEYS',out[0]['record'].keys())
for a in out: print('\nID',a['id'],json.dumps(a['record'],ensure_ascii=False))
