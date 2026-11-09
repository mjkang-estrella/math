import random,itertools,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(228);out=[]
for c in range(4,11):
 pairs=list(itertools.combinations(range(c),2));best=(0,1)
 for nv in (9,21,51):
  worst=0;arg=None
  for rep in range(300):
   votes=[rng.sample(range(c),c) for _ in range(nv)];counts=[[0]*c for _ in pairs]
   for vote in votes:
    rank=[vote.index(a) for a in range(c)]
    for z,(i,j) in enumerate(pairs):
     for a in range(c):counts[z][a]+=rank[a]<min(rank[i],rank[j])
   val=min(map(max,counts));worst=max(worst,val)
   if val*3>nv*2:arg=votes;break
  o=dict(candidates=c,voters=nv,profiles=rep+1,best_minimum_committee_domination_count=worst,strictly_above_two_thirds=arg is not None);out.append(o);print(o,flush=True)
  if arg is not None:(D/'election-lead.json').write_text(json.dumps(arg));raise RuntimeError('lead needs source example screen')
(D/'election-coverage.json').write_text(json.dumps(out,indent=2)+'\n')
