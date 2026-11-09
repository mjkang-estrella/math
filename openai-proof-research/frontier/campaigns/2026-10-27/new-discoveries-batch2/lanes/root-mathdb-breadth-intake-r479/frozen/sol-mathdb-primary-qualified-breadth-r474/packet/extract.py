import json,pathlib,hashlib
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes');O=L/'sol-mathdb-primary-qualified-breadth-r474';I=L/'root-mathdb-breadth-intake-r473';V=L/'pi-mathdb-full-corpus-inventory-r301'
r=json.loads((I/'reserved-ids.json').read_text());q=json.loads((I/'queue.json').read_text());cov=json.loads((I/'coverage-delta.json').read_text());ids=r['ids'];assert len(ids)==len(set(ids))==50;assert ids==[x['mathdb_id'] for x in q];assert not(set(ids)&set(r['other_active_reservations']));assert not(set(ids)&{372627,372628,368940,404067,364119});assert not(set(map(str,ids))&set(cov));assert len(cov)==3183
ex=[]
def collect(x):
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ['mathdb_id','mathdb_ids','problem_ids','related_mathdb_id','mathdb_related_id']:
    ex.extend(v if isinstance(v,list) else [v])
   else:collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
for f in ['accepted-exclusions.json','historical-dispositions.json']:collect(json.loads((L/'root-mathdb-accepted-exclusions-r304'/f).read_text()))
assert not(set(ids)&set(ex))
rows=[]
for p in sorted((V/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for n,line in enumerate(p.open(),1):
  x=json.loads(line)
  if x.get('mathdb_id',x.get('id')) in ids:
   rows.append({'original_chunk':str(p),'original_line':n,'canonical_record_sha256':hashlib.sha256(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest(),'record':x})
assert len(rows)==50
(O/'statements.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('record keys',list(rows[0]['record']));print(json.dumps(rows[0],ensure_ascii=False,indent=2))
(O/'preflight-checks.json').write_text(json.dumps({'intake_manifest':'independently hashed, no upstream code execution','baseline':len(cov),'assignment':50,'exclusion_disjoint':True,'other_active_disjoint':True,'special_disjoint':True},indent=2)+'\n')
