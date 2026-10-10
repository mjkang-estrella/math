"""Finite exact diagnostics only. Universal proofs and novelty are in the report."""
from fractions import Fraction as F
from itertools import product,combinations
from collections import defaultdict

def rank(a):
 a=[[F(x) for x in row] for row in a];h=0
 for j in range(len(a[0])):
  k=next((k for k in range(h,len(a)) if a[k][j]),None)
  if k is None:continue
  a[h],a[k]=a[k],a[h];c=a[h][j];a[h]=[x/c for x in a[h]]
  for k in range(len(a)):
   if k!=h:
    c=a[k][j];a[k]=[x-c*y for x,y in zip(a[k],a[h])]
  h+=1
  if h==len(a):break
 return h

def matrices(n,p):
 pairs=list(combinations(range(n),2))+[(i,i) for i in range(n)]
 for bits in product((-1,1),repeat=len(pairs)):
  a=[[0]*n for _ in range(n)]
  for (i,j),b in zip(pairs,bits):a[i][j]=a[j][i]=b
  plus=bits.count(1);yield a,p**plus*(1-p)**(len(bits)-plus)

def run():
 counts=defaultdict(int)
 for p in (F(1,4),F(1,3),F(1,2),F(3,4)):
  q=1-p;r=max(p,q);s=min(p,q);Q=p*p+q*q;c3=p**3+q**3
  ap=max(3*r*r*s,r**3+2*r*s*s);assert ap<Q
  for coeff in product((-2,-1,1,2),repeat=3):
   atoms=defaultdict(F)
   for bits in product((-1,1),repeat=3):
    atoms[sum(x*y for x,y in zip(coeff,bits))]+=p**bits.count(1)*q**bits.count(-1)
   assert max(atoms.values())<=ap;counts['three_coefficient_small_ball']+=1
  for n in (2,3,4):
   probplus=probminus=un=F(0);quot=defaultdict(F);proprank=F(0)
   for a,w in matrices(n,p):
    plus=a[0]==a[1];minus=all(x==-y for x,y in zip(a[0],a[1]))
    pairs=[(i,j,e) for i,j in combinations(range(n),2) for e in (-1,1) if all(x==e*y for x,y in zip(a[i],a[j]))]
    if pairs:un+=w
    if plus:
     probplus+=w;ind=[0]+list(range(2,n));b=[[a[i][j] for j in ind] for i in ind]
     assert rank(a)==rank(b);quot[tuple(map(tuple,b))]+=w
     if rank(b)<n-1:proprank+=w
     counts['planted_equal_pair_rank']+=1
    if minus:
     probminus+=w
     if p==F(1,2):
      d=[1,-1]+[1]*(n-2);aa=[[a[i][j]*d[i]*d[j] for j in range(n)] for i in range(n)]
      assert aa[0]==aa[1] and rank(aa)==rank(a);counts['fair_opposite_congruence']+=1
   assert probplus==c3*Q**(n-2) and probminus==p*q*(2*p*q)**(n-2)
   for b,w in quot.items():
    theory=F(1)
    for i in range(n-1):
     for j in range(i,n-1):
      pp=p**3/c3 if i==j==0 else p*p/Q if i==0 else p
      theory*=pp if b[i][j]==1 else 1-pp
    assert w/probplus==theory;counts['exact_conditional_quotient_law']+=1
   if p==F(1,2):
    sing=sum(w for b,w in matrices(n-1,p) if rank(b)<n-1)
    assert proprank/probplus==sing;counts['fair_exact_corank_transfer']+=1
   L=F(n*(n-1),2)*(probplus+probminus)
   assert un<=L
   if n>=4:
    lam=max(c3,Q*Q);assert L-un<=2*n**4*lam**(n-4)
   counts['pair_probabilities_and_union']+=1
  # A nontrivial partition with two classes of size two, signed at fairness.
  n=4;classes=[0,0,1,1];ds=([1,-1,1,-1] if p==F(1,2) else [1]*4)
  joint=defaultdict(F);mass=F(0)
  for a,w in matrices(n,p):
   aa=[[a[i][j]*ds[i]*ds[j] for j in range(n)] for i in range(n)]
   if aa[0]!=aa[1] or aa[2]!=aa[3]:continue
   b=((aa[0][0],aa[0][2]),(aa[2][0],aa[2][2]));joint[b]+=w;mass+=w
   assert rank(a)==rank(b);counts['partition_rank_identity']+=1
  for b,w in joint.items():
   theory=F(1)
   for i,j,weight in [(0,0,3),(0,1,4),(1,1,3)]:
    pp=p**weight/(p**weight+q**weight)
    theory*=pp if b[i][j]==1 else 1-pp
   assert w/mass==theory;counts['partition_conditional_block_law']+=1
 return dict(status='PASS',counts=dict(sorted(counts.items())),scope='Finite exact rational identities and enumerations only; no universal proof, asymptotic estimate, conditional classification of all singularity, or substantiality certification')
if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2))
