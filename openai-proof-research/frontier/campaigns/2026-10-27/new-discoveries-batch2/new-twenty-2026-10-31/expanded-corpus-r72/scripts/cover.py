import pathlib,json,itertools,numpy as np
from scipy.optimize import linprog
D=pathlib.Path(__file__).resolve().parents[1];k=2;points=list(itertools.product(range(k),repeat=3));lines=[[i for i,p in enumerate(points) if all(p[j]==v for j,v in zip([j for j in range(3) if j!=axis],ab))] for axis in range(3) for ab in itertools.product(range(k),repeat=2)];lm=[sum(1<<i for i in l) for l in lines];A=np.array([[int(i in l) for i in range(8)] for l in lines]);bad=[];qualified=0;tested=0
for S in range(1,16):
 active=sum(1<<i for i,p in enumerate(points) if S>>(p[0]*2+p[1])&1)
 for H in range(256):
  if H&~active:continue
  tested+=1;t=S.bit_count();rho=None
  for c in range(t+1):
   if any((__import__('functools').reduce(int.__or__,C,0)&H)==H for C in itertools.combinations(lm,c)):rho=c;break
  if rho!=t:continue
  qualified+=1;eq=[8+a for a in range(4) if S>>a&1];ok=False
  for a,b in [(1,1),(1,2),(2,1),(1,3),(3,1),(1,4),(4,1),(1,8),(8,1)]:
   r=[a,b];caps=np.array([r[p]*r[q] for ax in range(3) for p,q in itertools.product(range(2),repeat=2)])
   res=linprog(np.zeros(8),A_ub=A,b_ub=caps,A_eq=A[eq],b_eq=caps[eq],bounds=[(0,None) if H>>i&1 else (0,0) for i in range(8)],method='highs',options={'threads':1})
   if res.success:ok=True;break
  if not ok:bad.append({'S':S,'H':H})
out=dict(k=k,H_restricted_to_S_times_k=True,tested_pairs=tested,cover_condition_pairs=qualified,integer_class_sizes_tested=[[1,1],[1,2],[2,1],[1,3],[3,1],[1,4],[4,1],[1,8],[8,1]],unresolved_pairs=bad,note='LP diagnostics use real weights; rational/integer reconstruction and source equivalence not formalized')
(D/'outputs/cover.json').write_text(json.dumps(out,indent=2));print(out)
