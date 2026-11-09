from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]
s=(D/'scripts/lattice.py').read_text();exec(s[:s.index('rows=[]')])
rows=[];n=6;Oall=orders(n)
graphs=[('path',[(i,i+1) for i in range(5)]),('cycle',[(i,(i+1)%6) for i in range(6)]),('star',[(0,i) for i in range(1,6)]),('K33',[(i,j) for i in range(3) for j in range(3,6)])]
for name,edges in graphs:
 adj=[0]*n
 for i,j in edges:adj[i]|=1<<j;adj[j]|=1<<i
 c={s:connected(s,adj) for s in range(1,1<<n)};O=[r for r in Oall if all(c[s] for s in r)];up=[]
 for r in O:up.append(sum(1<<j for j,s in enumerate(O) if all(x&y==x for x,y in zip(r,s))))
 U=set(up);bad=None
 for i,a in enumerate(up):
  for j in range(i):
   if a&up[j] not in U:bad=(i,j);break
  if bad:break
 row=dict(n=6,name=name,edges=edges,ornamentations=len(O),join_failure=bad)
 if bad:row['witness']=[O[x] for x in bad]
 rows.append(row);print(row,flush=True);(D/'outputs/lattice6.json').write_text(json.dumps(rows,indent=2))
 if bad:break
