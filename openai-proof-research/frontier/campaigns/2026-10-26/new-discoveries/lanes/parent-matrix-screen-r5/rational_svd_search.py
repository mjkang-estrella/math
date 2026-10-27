#!/usr/bin/env python3
from pathlib import Path
import json, numpy as np, sympy as s
p=Path(__file__).resolve().parent
j=json.loads((p/'lin-optimized-absolute.json').read_text())
Ad=np.diag(j['A']);Bd=np.array(j['B']);u,dd,vh=np.linalg.svd(Ad@Bd);qo=vh@u;ko=(qo-np.eye(3))@np.linalg.inv(qo+np.eye(3));ao=vh@Ad@vh.T
print('D',dd,'K',ko,'A',ao,flush=True)
x,y,z=s.symbols('x y z')
best=None
for den in [2,3,4,5,6,8,10,12,16,20,25,40,50,100]:
 ks=[s.Rational(round(ko[i,j]*den),den)for i,j in [(0,1),(0,2),(1,2)]]
 K=s.Matrix([[0,ks[0],ks[1]],[-ks[0],0,ks[2]],[-ks[1],-ks[2],0]])
 Q=(s.eye(3)-K).inv()*(s.eye(3)+K)
 for ds in [[s.Rational(round(dd[0]*d),d),s.Rational(round(dd[1]*d),d),0]for d in [2,4,8,10,20]]:
  if ds[0]<=ds[1]or ds[1]<=0:continue
  D=s.diag(*ds);X=Q*D
  for da in [2,3,4,5,8,10,20]:
   diag=[s.Rational(round(ao[i,i]*da),da)for i in range(3)]
   A=s.Matrix([[diag[0],x,y],[x,diag[1],z],[y,z,diag[2]]]);H=X*A-A*X.T
   try:sol=s.solve([H[0,1],H[0,2],H[1,2]],[x,y,z]);A=A.subs(sol)
   except Exception:continue
   if A.free_symbols:continue
   Af=np.array(A,float)
   if min(np.linalg.eigvalsh(Af))<.01:continue
   B=A.inv()*X;Bf=np.array(B,float)
   if np.max(np.abs(Bf-Bf.T))>1e-10 or min(np.linalg.eigvalsh(Bf))< -1e-9:continue
   L=A*A+Q*(D**3)*Q.T;R=A*A+D**3
   gap=float(np.linalg.eigvalsh(np.array(L,float))[0]-np.linalg.eigvalsh(np.array(R,float))[0])
   if gap>1e-4:
    cost=max(len(str(v))for M in [A,B,Q,D] for v in M)
    if best is None or cost<best['max_entry_chars']:
     best={'K':[[str(v)for v in K.row(i)]for i in range(3)],'Q':[[str(v)for v in Q.row(i)]for i in range(3)],'D':list(map(str,ds)),'A':[[str(v)for v in A.row(i)]for i in range(3)],'B':[[str(v)for v in B.row(i)]for i in range(3)],'gap_float':gap,'max_entry_chars':cost,'L':[[str(v)for v in L.row(i)]for i in range(3)],'R':[[str(v)for v in R.row(i)]for i in range(3)]}
     (p/'lin-rational-svd.json').write_text(json.dumps(best,indent=2)+'\n');print('BEST',den,ds,da,gap,cost,flush=True)
print('FINAL',json.dumps(best))
