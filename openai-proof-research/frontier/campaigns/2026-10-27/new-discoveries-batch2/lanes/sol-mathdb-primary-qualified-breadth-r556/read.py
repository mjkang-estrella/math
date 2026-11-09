import json,pathlib,hashlib
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r555';C=L/'pi-mathdb-full-corpus-inventory-r301'
j=lambda p:json.loads(p.read_text())
q=j(I/'queue.json'); ids={r['mathdb_id'] for r in q};assert ids==set(j(I/'reserved-ids.json')['ids']) and len(ids)==50
cov=j(I/'coverage-delta.json');assert len(cov)==4833
seen=set()
for r in j(I/'active-breadth-reservations.json'):
 s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
rows=[]
for e in j(C/'manifest.json')['files']:
 if not e['path'].startswith('corpus/'):continue
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   rows.append({'mathdb_id':r['mathdb_id'],'chunk':str(p),'line':n,'record':r,'statement':r['statement'],'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50
rows.sort(key=lambda r:[x['mathdb_id'] for x in q].index(r['mathdb_id']))
(O/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(O/'reading.txt').write_text('\n\n'.join(str(i+1)+' ID '+str(r['mathdb_id'])+' '+r['record'].get('title','')+'\n'+r['statement']+'\nSOURCES '+str({k:v for k,v in r['record'].items() if 'source' in k}) for i,r in enumerate(rows)))
print((O/'reading.txt').read_text())
