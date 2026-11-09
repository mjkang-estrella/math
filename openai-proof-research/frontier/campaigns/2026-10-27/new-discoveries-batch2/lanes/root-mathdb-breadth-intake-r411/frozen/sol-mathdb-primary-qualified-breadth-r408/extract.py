import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent;I=L.parent/'root-mathdb-breadth-intake-r407'
r=json.loads((I/'reserved-ids.json').read_text()); ids=set(r['ids']);cov=json.loads((I/'coverage-delta.json').read_text());q=json.loads((I/'queue.json').read_text())
assert len(ids)==50 and len(cov)==1583 and not ids&set(map(int,cov)) and not ids&set(r['other_active_reservations']) and not ids&{372627,372628,368940} and ids=={x['mathdb_id'] for x in q}
found=[]
for path in json.loads((L/'bindings.json').read_text())['corpus_chunks']:
 with open(path) as f:
  for line in f:
   row=json.loads(line)
   if row.get('id',row.get('mathdb_id')) in ids:
    found.append({'record':row,'corpus_path':path,'line_sha256':hashlib.sha256(line.encode()).hexdigest()})
assert len(found)==50
(L/'records.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
(L/'assignment-check.json').write_text(json.dumps({'ids':sorted(ids),'reviewed_count':len(cov),'other_active_count':len(r['other_active_reservations']),'exactset':True,'disjoint':True},indent=2)+'\n')
print(json.dumps(found[0],ensure_ascii=False,indent=2))
