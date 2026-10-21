from diagnostic import *
from math import prod
from pathlib import Path

def rref(A):
 a=[[F(v) for v in row] for row in A]; piv=[];i=0
 for j in range(len(a[0])):
  k=next((k for k in range(i,len(a)) if a[k][j]),None)
  if k is None:continue
  a[i],a[k]=a[k],a[i];z=a[i][j];a[i]=[v/z for v in a[i]]
  for k in range(len(a)):
   if k!=i and a[k][j]:
    z=a[k][j];a[k]=[x-z*y for x,y in zip(a[k],a[i])]
  piv.append(j);i+=1
  if i==len(a):break
 return a,piv

def nullspace(A):
 a,piv=rref(A);free=[i for i in range(len(a[0])) if i not in piv];out=[]
 for j in free:
  v=[F(0)]*len(a[0]);v[j]=F(1)
  for row,p in enumerate(piv):v[p]=-a[row][j]
  assert all(sum(x*y for x,y in zip(row,v))==0 for row in A)
  out.append(v)
 return out

def uncollided(S,m,pts,p=1000003):
 # Ordinary derivatives; evaluated modulo p. Bases x^K*y^j with possibly negative K.
 A=[]
 for x,y in pts:
  for b in range(m):
   for ell in range(m-b):
    A.append([(prod(range(k-ell+1,k+1))*prod(range(j-b+1,j+1))*pow(x,k-ell,p)*pow(y,j-b,p))%p for j,k in S])
 return A

if __name__=='__main__':
 r,d,m=13,11,3;S,I,A=matrix(r,d,m);ns=nullspace(list(map(list,zip(*A))));rank=len(I)-len(ns)
 result={'case':[r,d,m],'rank_Q':rank,'rows':len(I),'columns':len(S),'S':S,'row_indices':I,'left_nullvectors':[[str(c) for c in v] for v in ns],'delta_tests':[]}
 print('EXACT RANK',rank)
 for v in ns:print('NULL POLYNOMIAL',[(str(c),I[i]) for i,c in enumerate(v) if c])
 for delta in [F(1,1000),F(1,100),F(1,10),F(1,4),F(49,100)]:
  ss,ii,aa=matrix(r,d,m,delta);z=rank_mod(aa);result['delta_tests'].append([str(delta),z]);print('DELTA',delta,'modrank',z)
 pts=[(1,1),(2,3),(3,2),(4,4)]
 un=uncollided(S,m,pts);z=rank_mod(un);print('UNCOLLIDED modrank',z,'shape',len(un),len(S));result['uncollided']={'points':pts,'prime':1000003,'rank_mod':z}
 # Full-rank residue witnesses are characteristic-zero nonvanishing certificates; deficiency alone is not.
 (Path(__file__).resolve().parents[1]/'scratch/finite-repair.json').write_text(json.dumps(result,indent=2))
