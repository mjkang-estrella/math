exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('bound={}')[0])
q=j(I/'queue-r694.json');ids={r['mathdb_id'] for r in q};res=j(I/'reserved-ids-r694.json');assert ids==set(res['ids']) and len(ids)==50
cov=j(I/'coverage-delta.json');assert len(cov)==8233 and not ids&set(map(int,cov))
a=j(I/'active-breadth-reservations.json');seen=set()
for r in a:
 s=set(r['ids']);assert not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
print('DISJOINT',[(r['lane'],len(r['ids'])) for r in a])
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',I/'adjudications.json',I/'hypothesis-queue.json',L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 o=p.read_text(); print('CONTEXT',p.name,o[:18000])
rows=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   rows.append({'mathdb_id':r['mathdb_id'],'chunk':str(p.relative_to(C)),'line':n,'record':r});print('RECORD',r['mathdb_id'],str(p.relative_to(C)),n,json.dumps(r,ensure_ascii=False))
assert len(rows)==50
write('literal-records.json',rows)
