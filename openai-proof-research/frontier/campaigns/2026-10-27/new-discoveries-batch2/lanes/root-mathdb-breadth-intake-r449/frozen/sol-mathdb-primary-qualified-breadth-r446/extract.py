import pathlib,json,hashlib
R=pathlib.Path(__file__).resolve().parent;L=R.parent;I=L/'root-mathdb-breadth-intake-r445'
res=json.loads((I/'reserved-ids.json').read_text());ids=res['ids'];cov=json.loads((I/'coverage-delta.json').read_text());assert len(ids)==len(set(ids))==50;assert len(cov)==2533
assert not set(ids)&(set(map(int,cov))|set(res['other_active_reservations'])|{372627,372628,368940,404067,364119})
records=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for idx,line in enumerate(p.open(),1):
  j=json.loads(line)
  if j['mathdb_id'] in ids:records.append({'record':j,'original':str(p.resolve()),'line':idx,'literal_sha256':hashlib.sha256(j['statement'].encode()).hexdigest(),'canonical_sha256':hashlib.sha256(json.dumps(j,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()})
assert sorted(x['record']['mathdb_id'] for x in records)==sorted(ids)
(R/'assigned-records.json').write_text(json.dumps(records,indent=2,ensure_ascii=False)+'\n')
(R/'statements.txt').write_text('\n\n'.join(f"ID {x['record']['mathdb_id']} {x['record']['title']}\n{x['record']['statement']}\nSOURCE {x['record']['source_url']}\nREF {x['record']['references']}" for x in records)+'\n')
print((R/'statements.txt').read_text())
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 j=json.loads((L/'root-mathdb-accepted-exclusions-r304'/n).read_text());print(n,'keys',list(j) if isinstance(j,dict) else 'list')
