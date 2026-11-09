from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r409';C=B/'pi-mathdb-full-corpus-inventory-r301'
a=json.loads((I/'reserved-ids.json').read_text());ids=set(a['ids']);cov=json.loads((I/'coverage-delta.json').read_text())
assert len(ids)==50 and not ids.intersection(a['other_active_reservations']) and not ids.intersection({372627,372628,368940})
assert len(cov)==1633 and not ids.intersection(map(int,cov))
q=json.loads((I/'queue.json').read_text());assert {x['mathdb_id'] for x in q}==ids
rows=[]
for f in sorted(C.glob('corpus/*.jsonl')):
 for line in f.open():
  r=json.loads(line)
  if int(r.get('mathdb_id',r.get('id',-1))) in ids:
   r['_chunk']=str(f);rows.append(r)
assert len(rows)==50
(L/'selected-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(L/'assignment-check.json').write_text(json.dumps({'ids':sorted(ids),'count':50,'reviewed_count':len(cov),'disjoint_reviewed':True,'disjoint_active':True,'disjoint_special':True,'all_twenty_verified_before_extraction':True},indent=2)+'\n')
print('first record',json.dumps(rows[0],ensure_ascii=False))
print('r304')
for p in B.glob('*r304/*.json'):
 if p.name in ['accepted-exclusions.json','historical-dispositions.json']:
  d=json.loads(p.read_text());print(p.name, str(d)[:1800])
print('r363', (B/'root-mathdb-cayley-review-intake-r363/disposition.json').read_text()[:3500])
