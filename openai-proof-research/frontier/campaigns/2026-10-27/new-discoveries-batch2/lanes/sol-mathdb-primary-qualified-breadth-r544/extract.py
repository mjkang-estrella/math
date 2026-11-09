import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r543'
q=json.loads((I/'queue.json').read_text());res=json.loads((I/'reserved-ids.json').read_text());cov=json.loads((I/'coverage-delta.json').read_text());active=json.loads((I/'active-breadth-reservations.json').read_text())
ids={r['mathdb_id'] for r in q};assert len(ids)==50 and ids==set(res['ids']);assert len(cov)==4533
sets=[set(x['ids']) for x in active];assert sum(set(x['ids'])==ids for x in active)==1;print('reservation sizes',list(map(len,sets)))
for i,s in enumerate(sets):
 assert len(s)==50 and not s&set(map(int,cov)) and not s&set(res['protected_ids'])
 for t in sets[:i]:assert not s&t
rows=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   rows.append({'mathdb_id':r['mathdb_id'],'chunk':str(p),'line':n,'statement':r['statement'],'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
rows.sort(key=lambda r:r['mathdb_id']);assert len(rows)==50
(D/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(D/'reading.txt').write_text('\n\n'.join(str(r['mathdb_id'])+' | '+r['record']['title']+'\n'+r['statement']+'\nSOURCE '+str(r['record']['source_url']) for r in rows)+'\n')
print('extracted',len(rows))
