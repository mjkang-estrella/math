# Build integer certificates for the Lean proof that the 4x4x5 functional l defines a facet of P^{4,4,5}.
# Margin coordinates: ('12',i,j) i<4,j<4 ; ('13',i,k) i<4,k<5 ; ('23',j,k) j<4,k<5.
import json,itertools,sys
from fractions import Fraction
from math import lcm
p,q,r=4,4,5
A=[[0,0,0,0],[0,0,0,1],[0,0,1,1],[0,1,1,0]]
cert=json.load(open('outputs/collapsing-444r-certificates.json'))
ex=[o for o in cert if o['a']==A][0]
B=[[int(x) for x in row] for row in ex['functional']['b']]; C=[[int(x) for x in row] for row in ex['functional']['c']]
coords=[('12',i,j) for i in range(p) for j in range(q)]+[('13',i,k) for i in range(p) for k in range(r)]+[('23',j,k) for j in range(q) for k in range(r)]
ix={c:n for n,c in enumerate(coords)}
cells=[(i,j,k) for i in range(p) for j in range(q) for k in range(r)]
def col(c):
  i,j,k=c; v=[0]*56; v[ix[('12',i,j)]]=1; v[ix[('13',i,k)]]=1; v[ix[('23',j,k)]]=1; return v
w={c:A[c[0]][c[1]]+B[c[0]][c[2]]+C[c[1]][c[2]] for c in cells}
assert min(w.values())>=0
tight=[c for c in cells if w[c]==0]; nont=[c for c in cells if w[c]>0]
def rref_rank(vs):
  M=[list(map(Fraction,v)) for v in vs]; piv=[]; rr=0
  for cc in range(len(M[0])):
    pr=next((t for t in range(rr,len(M)) if M[t][cc]!=0),None)
    if pr is None: continue
    M[rr],M[pr]=M[pr],M[rr]; M[rr]=[x/M[rr][cc] for x in M[rr]]
    for t in range(len(M)):
      if t!=rr and M[t][cc]!=0: f=M[t][cc]; M[t]=[x-f*y for x,y in zip(M[t],M[rr])]
    piv.append(cc); rr+=1
  return rr,piv,M[:rr]
# greedy independent subset of tight columns
basis=[]
for c in tight:
  if rref_rank([col(x) for x in basis+[c]])[0]==len(basis)+1: basis.append(c)
assert len(basis)==43, len(basis)
# dual functionals: pick 43 coordinates where the submatrix is invertible, invert
Vt=[col(c) for c in basis]  # 43 x 56
_,pivcols,_=rref_rank([[Vt[t][m] for t in range(43)] for m in range(56)])  # rows = coordinates; pivots = basis indices (all 43)
# choose 43 coordinates R with invertible 43x43 matrix: greedy
R=[]
for m in range(56):
  rows=[[Vt[t][mm] for t in range(43)] for mm in R+[m]]
  if rref_rank(rows)[0]==len(R)+1: R.append(m)
  if len(R)==43: break
Msub=[[Fraction(Vt[t][m]) for t in range(43)] for m in R]  # Msub[a][t] = v_t(R_a)
# invert: find X (43x43) with sum_a X[s][a]*Msub[a][t] = delta_st
n=43; aug=[Msub[a][:]+[Fraction(int(a==b)) for b in range(n)] for a in range(n)]
# solve X * Msub = I  <=> Msub^T X^T = I
MT=[[Msub[a][t] for a in range(n)] for t in range(n)]
aug=[MT[t][:]+[Fraction(int(t==s)) for s in range(n)] for t in range(n)]
for c in range(n):
  pr=next(t for t in range(c,n) if aug[t][c]!=0); aug[c],aug[pr]=aug[pr],aug[c]
  aug[c]=[x/aug[c][c] for x in aug[c]]
  for t in range(n):
    if t!=c and aug[t][c]!=0: f=aug[t][c]; aug[t]=[x-f*y for x,y in zip(aug[t],aug[c])]
XT=[row[n:] for row in aug]  # XT[a][s] = X[s][a]
D=1
for row in XT:
  for x in row: D=lcm(D,x.denominator)
Phi=[[0]*56 for _ in range(n)]
for s in range(n):
  for a,m in enumerate(R): Phi[s][m]=int(XT[a][s]*D)
for s in range(n):
  for t in range(n): assert sum(Phi[s][m]*Vt[t][m] for m in range(56))==(D if s==t else 0)
c0=nont[0]
# margin relations psi (12) in RREF with pivot coordinates
rels=[]
for i in range(p): v=[0]*56; [v.__setitem__(ix[('12',i,j)],1) for j in range(q)]; [v.__setitem__(ix[('13',i,k)],-1) for k in range(r)]; rels.append(v)
for j in range(q): v=[0]*56; [v.__setitem__(ix[('12',i,j)],1) for i in range(p)]; [v.__setitem__(ix[('23',j,k)],-1) for k in range(r)]; rels.append(v)
for k in range(r): v=[0]*56; [v.__setitem__(ix[('13',i,k)],1) for i in range(p)]; [v.__setitem__(ix[('23',j,k)],-1) for j in range(q)]; rels.append(v)
rk,piv,RR=rref_rank(rels); assert rk==12
Psi=[[int(x) for x in row] for row in RR]; assert all(x.denominator==1 for row in RR for x in row)
for s in range(12):
  for c in cells: assert sum(Psi[s][m]*col(c)[m] for m in range(56))==0
  for t in range(12): assert Psi[s][piv[t]]==int(s==t)
pats=[frozenset((i,j) for i in range(p) for j in range(q) if w[(i,j,k)]==0) for k in range(r)]
assert len(set(pats))==5
out=dict(A=A,B=B,C=C,D=D,basis=basis,c0=c0,w_c0=w[c0],coords=coords,Phi=Phi,Psi=Psi,psi_pivots=piv,R=R,tight=len(tight),maxabsPhi=max(abs(x) for row in Phi for x in row))
json.dump(out,open('outputs/lean-certificate-445.json','w'),indent=1)
print('D',D,'maxPhi',out['maxabsPhi'],'c0',c0,w[c0],'psi piv',piv,'nonzeros Phi',sum(1 for row in Phi for x in row if x))
