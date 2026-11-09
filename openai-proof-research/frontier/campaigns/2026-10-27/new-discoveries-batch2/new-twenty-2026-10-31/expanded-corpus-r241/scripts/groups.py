from pathlib import Path
import sys,itertools,math
D=Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'))
import z3
for mod in [(2,2,3),(2,2,5),(2,2,2,3),(4,2,3),(2,2,7)]:
 els=list(itertools.product(*[range(m) for m in mod]))[1:];n=len(els);counts={}
 for a in range(n//3+1):
  for b in range(n//4+1):
   if (n-3*a-4*b)<0 or (n-3*a-4*b)%5:continue
   c=(n-3*a-4*b)//5;sizes=[3]*a+[4]*b+[5]*c
   s=z3.Solver();s.set(timeout=900);x=[z3.Int('x'+str(i)) for i in range(n)]
   for v in x:s.add(v>=0,v<len(sizes))
   for j,sz in enumerate(sizes):
    s.add(z3.Sum([z3.If(v==j,1,0) for v in x])==sz)
    for k,m in enumerate(mod):s.add(z3.Sum([z3.If(x[i]==j,els[i][k],0) for i in range(n)])%m==0)
   r=str(s.check());counts[r]=counts.get(r,0)+1;print('CASE',mod,sizes,r,flush=True)
 print('ROW',mod,counts,flush=True)
