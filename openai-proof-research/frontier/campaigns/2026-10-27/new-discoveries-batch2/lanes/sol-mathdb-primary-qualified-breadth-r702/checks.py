import json,pathlib
D=pathlib.Path(__file__).parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r701'
def load(p):return json.loads(p.read_text())
q=load(I/'queue-r702.json');ids={e['mathdb_id'] for e in q};reserved=load(I/'reserved-ids-r702.json');print('reservation schema',type(reserved).__name__)
a=load(I/'active-breadth-reservations.json');coverage=set(map(int,load(I/'coverage-delta.json')));assert len(coverage)==8433
sets=[set(e['ids']) for e in a];assert len(ids)==50 and ids==sets[2]
for i,s in enumerate(sets):
 assert len(s)==50 and not s&coverage and not s&set(a[i]['protected_ids'])
 for t in sets[i+1:]:assert not s&t
assert ids==set(reserved if isinstance(reserved,list) else reserved['ids'])
rids=set()
def walk(x):
 if isinstance(x,dict):
  for k,v in x.items():
   if str(k).isdigit():rids.add(int(k))
   if k in ['mathdb_id','id'] and str(v).isdigit():rids.add(int(v))
   walk(v)
 elif isinstance(x,list):
  for y in x:walk(y)
for n in ['accepted-exclusions.json','historical-dispositions.json']:walk(load(L/'root-mathdb-accepted-exclusions-r304'/n))
print('R304 assigned matching',sorted(ids&rids))
print('ledger',load(L.parent/'ledger.json'))
print('prior context',load(L.parent/'prior-campaign-context.json'))
print('upstream',load(L.parents[4]/'sources/upstream.json'))
print('catalogue header', (L.parents[4]/'sources/CONTENTS.md').read_text()[:1500])
(D/'reservation-checks.json').write_text(json.dumps({'baseline':len(coverage),'sets':[len(s) for s in sets],'pairwise_disjoint':True,'coverage_disjoint':True,'protected_disjoint':True,'r304_matches':sorted(ids&rids),'timing_deviation':'Semantic reservation check after first literal reading; all bytes bound before reading.'},indent=2)+'\n')
