import pathlib,itertools,json,sys
from circulant_search import check
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in [15,22,23,24,31,32]:
 stats={};survivors=[];hits=[]
 for mask in range(1<<(n//2)):
  pos=[i+1 for i in range(n//2) if mask>>i&1];S=sorted(set(pos)|{n-s for s in pos});r=check(n,S,100000)
  label='success' if r.get('success') else ('triangle' if r.get('triangle') else ('diameter_gt2' if r.get('diameter_gt2') else 'path_failure_or_cap'))
  stats[label]=stats.get(label,0)+1
  if label=='path_failure_or_cap':survivors.append(dict(S=S,**r))
  if label=='success':hits.append(dict(S=S,**r))
 row=dict(n=n,stats=stats,failures=survivors,successes=hits);out.append(row);print(n,stats,[(x['S'],x['nodes'],x['first_uncovered']) for x in survivors],flush=True);(D/'outputs/circulant-exhaustive.json').write_text(json.dumps(out,indent=2))
