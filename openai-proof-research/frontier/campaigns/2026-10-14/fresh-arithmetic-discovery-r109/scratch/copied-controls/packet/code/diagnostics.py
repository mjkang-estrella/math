"""Bounded exact checks supporting notes; no asymptotic or theorem gate.
Read-only stdout, standard library only, no imported predecessor code.
"""
from fractions import Fraction
from itertools import combinations
import json,math

def rank(rows,p=0):
 if not rows:return 0
 a=[[Fraction(x) if not p else x%p for x in row] for row in rows]
 r=0
 for c in range(len(a[0])):
  k=next((k for k in range(r,len(a)) if a[k][c]),None)
  if k is None:continue
  a[r],a[k]=a[k],a[r]
  inv=1/a[r][c] if not p else pow(a[r][c],-1,p)
  a[r]=[x*inv if not p else x*inv%p for x in a[r]]
  for k in range(len(a)):
   if k==r:continue
   v=a[k][c]
   a[k]=[x-v*y if not p else (x-v*y)%p for x,y in zip(a[k],a[r])]
  r+=1
  if r==len(a):break
 return r

def flat_betti(t,p):
 # Basis 1,x,y,x^2; matrices independently encode displayed products.
 deg=[0,1,1,2]
 action=[{0:(1,1),1:(3,1)}, {0:(2,1),2:(3,t)}]
 betti={};checks=0
 for j in range(5):
  bases=[[(b,w) for b in range(4) for w in combinations(range(2),i) if deg[b]+i==j] for i in range(3)]
  ds={};rs={0:0,3:0}
  for i in [1,2]:
   target={u:k for k,u in enumerate(bases[i-1])}
   m=[[0]*len(bases[i]) for _ in bases[i-1]]
   for c,(b,w) in enumerate(bases[i]):
    for z,v in enumerate(w):
     if b in action[v]:
      b2,coeff=action[v][b];m[target[(b2,w[:z]+w[z+1:])]][c]+=(-1)**z*coeff
   ds[i]=m;rs[i]=rank(m,p)
  for a in range(len(bases[0])):
   for b in range(len(bases[2])):
    v=sum(ds[1][a][k]*ds[2][k][b] for k in range(len(bases[1])))
    assert (v%p if p else v)==0;checks+=1
  for i in range(3):
   v=len(bases[i])-rs[i]-rs[i+1]
   if v:betti[f'{i},{j}']=v
 return betti,checks
out=[]
for p in [0,2,3,5,7]:
 for t in [0,1]:
  b,c=flat_betti(t,p)
  expected={'0,0':1,'1,2':2,'2,4':1}
  if not t:expected.update({'1,3':1,'2,3':1})
  assert b==expected
  out.append({'characteristic':p,'t':t,'betti':b,'composition_checks':c})
# Check multinomial/no-carry support identity for binary forms in a bounded range.
power_checks=[]
for p in [2,3,5,7]:
 for b in range(2,21):
  support=[i for i in range(b+1) if math.comb(b,i)%p]
  no_carry=[]
  for i in range(b+1):
   a=i;c=b-i;yes=True
   while a or c:
    if a%p+c%p>=p:yes=False;break
    a//=p;c//=p
   if yes:no_carry.append(i)
  assert support==no_carry
  power_checks.append({'p':p,'degree':b,'support':support})
# Formal binary Frobenius substitution: expand h^q and compare g(U^q,V^q).
def mul(A,B,p):
 C={}
 for i,a in A.items():
  for j,b in B.items():C[i+j]=(C.get(i+j,0)+a*b)%p
 return {i:a for i,a in C.items() if a}
def power(A,q,p):
 C={0:1}
 for _ in range(q):C=mul(C,A,p)
 return C
curves=[]
for p,q in [(2,2),(2,4),(3,3),(5,5)]:
 for r in range(1,6):
  h={a:(a*a+r*a+r)%p for a in range(q+1)};h={a:c for a,c in h.items() if c}
  assert power(h,q,p)=={q*a:c for a,c in h.items()}
  curves.append({'p':p,'q':q,'coefficient_row':r})
print(json.dumps({'status':'bounded diagnostics only','flat_family':out,'binary_power_support_cases':power_checks,'frobenius_curve_identities':curves},indent=2))
