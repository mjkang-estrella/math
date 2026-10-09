"""Independent finite checks. No imported discovery code or third-party packages."""
from fractions import Fraction as F
from itertools import combinations
from math import factorial, sqrt, log
import cmath, json, random
from pathlib import Path
rng=random.Random(2026100802)

def mul_linear(poly, c, coeff):
 out={}
 for e,v in poly.items():
  if c:out[e]=out.get(e,F(0))+v*c
  for j,a in enumerate(coeff):
   if a:
    ee=list(e);ee[j]+=1;ee=tuple(ee)
    out[ee]=out.get(ee,F(0))+v*a
 return {e:v for e,v in out.items() if v}

def moment(power,variance):
 if power%2:return F(0)
 return F(factorial(power),2**(power//2)*factorial(power//2))*variance**(power//2)

def pairings(indices):
 if not indices:
  yield (),();return
 a,*tail=indices
 for pairs,singles in pairings(tail):yield pairs,(a,)+singles
 for j,b in enumerate(tail):
  for pairs,singles in pairings(tail[:j]+tail[j+1:]):yield ((a,b),)+pairs,singles

def wick(v,w):
 out=F(0)
 for pairs,singles in pairings(list(range(len(v)))):
  z=F((-1)**len(pairs))
  for a,b in pairs:z*=sum(x*y for x,y in zip(v[a],v[b]))
  for a in singles:z*=sum(x*y for x,y in zip(v[a],w))
  out+=z
 return out

conditional=[]
for s in range(1,9):
 for dim in ([1,2] if s<=4 else [1]):
  for trial in range(2):
   vectors=[[F(rng.randint(-3,3),rng.randint(1,3)) for _ in range(dim)] for _ in range(s)]
   w=[F(rng.randint(-3,3),2) for _ in range(dim)]
   poly={(0,)*(s*dim):F(1)}
   # sqrt(s) W_i | W_0=w has mean <v_i,w>. Represent residual with
   # independent Z_j,l of variance s and projection I - 11'/s.
   for i,v in enumerate(vectors):
    c=sum(a*b for a,b in zip(v,w))
    coeff=[(F(int(i==j))-F(1,s))*v[l] for j in range(s) for l in range(dim)]
    poly=mul_linear(poly,c,coeff)
   integral=F(0)
   for e,a in poly.items():
    for power in e:
     a*=moment(power,s)
     if not a:break
    integral+=a
   expected=wick(vectors,w)
   assert integral==expected,(s,dim,integral,expected)
   conditional.append({'s':s,'dim':dim,'trial':trial,'integrated_monomials':len(poly)})
# Distinguishes Wick from ordinary product and catches the missing sqrt(s) factor.
assert wick([[F(1)],[F(1)]],[F(0)]) == -1

# Rational rotation in R^2; complex spectral weights are usually nonreal.
def cpow(z,n):
 if n<0:return cpow((z[0],-z[1]),-n)
 out=(F(1),F(0))
 while n:
  if n&1:out=(out[0]*z[0]-out[1]*z[1],out[0]*z[1]+out[1]*z[0])
  z=(z[0]*z[0]-z[1]*z[1],2*z[0]*z[1]);n//=2
 return out
spectral_count=0;max_tv_ratio=0
for trial in range(12):
 a=[F(rng.randint(-3,3)) for _ in range(4)];b=[F(rng.randint(-3,3)) for _ in range(4)]
 tv=0
 for block,rot in enumerate([(F(3,5),F(4,5)),(F(5,13),F(12,13))]):
  aa=a[2*block:2*block+2];bb=b[2*block:2*block+2]
  A=aa[0]*bb[0]+aa[1]*bb[1];B=-aa[0]*bb[1]+aa[1]*bb[0]
  tv+=sqrt(float(A*A+B*B))
  for n in range(-6,7):
   # Difference of polynomial times, including constants and repeated values.
   power=(2*n*n+n-4)-(n*n-3*n+2)
   c,sn=cpow(rot,power)
   direct=aa[0]*(c*bb[0]-sn*bb[1])+aa[1]*(sn*bb[0]+c*bb[1])
   # ((A-iB)/2)e^{it} + ((A+iB)/2)e^{-it}
   spectral=A*c+B*sn
   assert direct==spectral
   spectral_count+=1
 bound=sqrt(float(sum(x*x for x in a)*sum(x*x for x in b)))
 assert tv<=bound+1e-12
 if bound:max_tv_ratio=max(max_tv_ratio,tv/bound)

# All partial pairings including fully paired cases and repeated vectors.
expansion_count=0;pair_counts=[]
for d in range(1,9):
 terms=list(pairings(list(range(d))));pair_counts.append(len(terms))
 for trial in range(5):
  v=[[F(rng.randint(-2,2)) for _ in range(2)] for _ in range(d)]
  w=[F(2,3),F(-1,2)]
  lhs=F(1)
  for vi in v:lhs*=sum(a*b for a,b in zip(vi,w))
  rhs=F(0)
  for pairs,singles in terms:
   term=F(1)
   for a,b in pairs:term*=sum(x*y for x,y in zip(v[a],v[b]))
   term*=wick([v[a] for a in singles],w);rhs+=term
  assert lhs==rhs
  expansion_count+=1
 assert len(terms)==sum(factorial(d)//(2**a*factorial(a)*factorial(d-2*a)) for a in range(d//2+1))

# Full finite variation via exhaustive subsequences, not adjacent increments.
subseq=[tuple(i for i in range(9) if mask>>i&1) for mask in range(1,1<<9)]
def var(seq,r):
 return max(sum(abs(seq[b]-seq[a])**r for a,b in zip(idx,idx[1:])) for idx in subseq)**(1/r)
variation_count=0;max_cond_ratio=0;max_complex_ratio=0
for r in (2.01,3,4):
 for trial in range(30):
  seqs=[[complex(rng.uniform(-2,2),rng.uniform(-2,2)) for _ in range(9)] for _ in range(4)]
  weights=[rng.random() for _ in range(4)];weights=[x/sum(weights) for x in weights]
  avg=[sum(weights[j]*seqs[j][n] for j in range(4)) for n in range(9)]
  rhs=sum(weights[j]*var(seqs[j],r) for j in range(4));lhs=var(avg,r)
  assert lhs<=rhs+1e-11
  max_cond_ratio=max(max_cond_ratio,lhs/rhs)
  complexweights=[complex(rng.uniform(-1,1),rng.uniform(-1,1)) for _ in range(4)]
  integ=[sum(complexweights[j]*seqs[j][n] for j in range(4)) for n in range(9)]
  rhs=sum(abs(complexweights[j])*var(seqs[j],r) for j in range(4));lhs=var(integ,r)
  assert lhs<=rhs+1e-11
  max_complex_ratio=max(max_complex_ratio,lhs/rhs);variation_count+=1

collision_count=0;individual_count=0;worst_ratio=0
for k in (1,2,3,5):
 for R in (1,2,7,31,100,1000):
  for N in (10,35,80):
   cutoff=int(sqrt(R));bad=0
   for n in range(1,N+1):
    for m in range(1,N+1):
     if n<=cutoff or m<=cutoff or any(abs(i*n*n-j*m*m)<R for i in range(1,k+1) for j in range(1,k+1)):bad+=1
    if n>sqrt(R):
     for i in range(1,k+1):
      for j in range(1,k+1):
       # An integer interval contains at most 1 + its length, with length <= 2R/n.
       count=sum(abs(i*n*n-j*m*m)<R for m in range(1,N+1))
       assert F(count)<=1+F(2*R,n)
       individual_count+=1
   bound=2*cutoff*N+k*k*(N+2*R*(1+log(N)))
   assert bad<=bound+1e-9
   worst_ratio=max(worst_ratio,bad/bound);collision_count+=1

out={'seed':2026100802,'conditional_projection_exact_cases':len(conditional),
'conditional_cases':conditional,'spectral_exact_cases':spectral_count,'spectral_TV_max_ratio':max_tv_ratio,
'ordinary_product_exact_cases':expansion_count,'partial_pairing_counts':pair_counts,
'variation_cases_each_type':variation_count,'largest_conditional_ratio':max_cond_ratio,
'largest_complex_measure_ratio':max_complex_ratio,'collision_rectangles':collision_count,
'individual_collision_bounds':individual_count,'largest_collision_bound_ratio':worst_ratio,
'verdict':'PASS finite checks only; no infinite theorem or novelty certification'}
print(json.dumps(out,indent=2))
