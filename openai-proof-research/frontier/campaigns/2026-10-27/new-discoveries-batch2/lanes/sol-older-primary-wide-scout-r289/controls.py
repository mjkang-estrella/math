from fractions import Fraction as F
from itertools import permutations,combinations
import pathlib,json
L=pathlib.Path(__file__).resolve().parent
def inertia(B):
 B=[[F(x) for x in r] for r in B];p=z=0
 while B:
  d=B[0][0]
  if d<0:return False,p,z
  if d==0:
   if any(B[0][1:]):return False,p,z
   z+=1;B=[r[1:] for r in B[1:]];continue
  p+=1;B=[[B[i][j]-B[i][0]*B[0][j]/d for j in range(1,len(B))] for i in range(1,len(B))]
 return True,p,z
def matrix(n,states,step):
 index={s:i for i,s in enumerate(states)};A=[[0]*len(states) for s in states]
 for k,s in enumerate(states):
  for i in range(n):
   for j in range(n):
    t=s
    for h in (range(i,j) if i<=j else range(i-1,j-1,-1)):t=step(t,h)
    A[k][index[t]]+=1
 return A
out=[]
for n in range(2,6):
 pairs=list(combinations(range(n),2));total=0;checked=0;skip=0
 for mask in range(1<<len(pairs)):
  rel={p for j,p in enumerate(pairs) if mask>>j&1}
  if any((a,c) not in rel for a,b in rel for b2,c in rel if b==b2):continue
  total+=1;states=[s for s in permutations(range(n)) if all(s.index(a)<s.index(b) for a,b in rel)]
  m=len(states)
  if m==1:continue
  if n==5 and m>12:skip+=1;continue
  def step(s,i):
   a,b=s[i:i+2]
   if (min(a,b),max(a,b)) in rel:return s
   t=list(s);t[i],t[i+1]=t[i+1],t[i];return tuple(t)
  A=matrix(n,states,step);assert A==list(map(list,zip(*A))) and all(sum(r)==n*n for r in A)
  b=n*n-n-2
  K=[[F(b*(i==j)-A[i][j]) for j in range(m)] for i in range(m)]
  R=[[K[i][j]-K[i][-1]-K[-1][j]+K[-1][-1] for j in range(m-1)] for i in range(m-1)]
  psd,p,z=inertia(R);assert psd,(n,rel)
  reach={0}
  while True:
   old=len(reach);reach|={b for a,b in rel if a in reach}|{a for a,b in rel if b in reach}
   if len(reach)==old:break
  connected=len(reach)==n;assert (z==0)==connected,(n,rel,z)
  checked+=1
 out.append(dict(n=n,naturally_labeled_posets=total,nonchain_checked=checked,skipped_above_12_extensions=skip))
# An irreducible abstract involution action violating the n=3 proposed bound.
# Alternating matchings on a 12-cycle satisfy the source's exponent-six relation.
states=list(range(12))
def step(s,h):return s^1 if h==0 else ((s-1)^1)+1 if s not in (0,11) else 11-s
for s in states:
 t=s
 for j in range(6):t=step(step(t,0),1)
 assert t==s
A=matrix(3,states,step);v=[1,1,1,0,-1,-1,-1,-1,-1,0,1,1];v=[F(x)-F(sum(v),12) for x in v]
Av=[sum(A[i][j]*v[j] for j in states) for i in states];ray=sum(v[i]*Av[i] for i in states)/sum(x*x for x in v)
assert ray>4
result={'poset_checks':out,'abstract_action_obstruction':{'n':3,'A':A,'zero_sum_vector':list(map(str,v)),'rayleigh_numerator_matrix':str(ray),'conjectured_bound_numerator':4},'scope':'Exact controls only. Source already numerically checked n<=7. No new source theorem.'}
(L/'checks.json').write_text(json.dumps(result,indent=2));print(json.dumps(result))
