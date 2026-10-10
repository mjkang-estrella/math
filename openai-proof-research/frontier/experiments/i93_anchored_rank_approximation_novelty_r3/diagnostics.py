#!/usr/bin/env python3
"""Independent finite diagnostics, no writes, randomness, or proof certification."""
from itertools import permutations,product
from fractions import Fraction as F
import json

def run():
 counts=dict(continuation_fixtures=0,endpoint_checks=0,variation_checks=0,loop_fixtures=0,mixed_badness_vertices=0,common_part_checks=0,adaptive_measure_checks=0,envelope_checks=0)
 # Enumerate actual matched walks (rather than reuse I90's record recurrence).
 for nv in (1,2,3):
  for perms in product(list(permutations(range(nv))),repeat=2):
   edges=[];out=[[] for _ in range(nv)]
   for perm in perms:
    for x,y in enumerate(perm):
     i=len(edges);edges.extend([(x,y,i+1),(y,x,i)]);out[x].append(i);out[y].append(i+1)
   for compatible in product((0,1),repeat=nv*2):
    for cross in (0,1):
     for depth in (2,3):
      records={}
      def paths(e,j,left):
       x,y,reverse=edges[e]
       if not compatible[2*x+j]:return []
       lengths=[]
       for k in range(2):
        if compatible[2*y+k] and (j==k or cross):
         lengths.append(1)
         if left>1:
          for f in out[y]:
           if f!=reverse:lengths.extend(1+a for a in paths(f,k,left-1))
       return lengths
      for e,j in product(range(len(edges)),range(2)):records[e,j]=max(paths(e,j,depth),default=0)
      bad={(x,j):max(records[e,j] for e in out[x])==depth for x,j in product(range(nv),range(2))}
      exc={(e,j):bad[edges[e][0],j] or records[e,j]>max(records[f,j] for f in out[edges[e][0]] if f!=e) for e,j in records}
      for x in range(nv):
       counts['mixed_badness_vertices']+=bad[x,0]!=bad[x,1]
       for j in range(2):assert bad[x,j] or sum(exc[e,j] for e in out[x])<=1
       for mu in [(1,0),(3,-1),(-2,3)]:
        tv=sum(map(abs,mu));w=sum(abs(mu[j])*bad[x,j] for j in range(2))
        lhs=sum(abs(mu[j])*exc[e,j] for e in out[x] for j in range(2))
        assert lhs<=tv+3*w  # sharper degree-four budget, no floating point
        counts['variation_checks']+=1
      for e,(x,y,rev) in enumerate(edges):
       for j,k in product(range(2),repeat=2):
        if compatible[2*x+j] and compatible[2*y+k] and (j==k or cross):
         assert exc[e,j] or exc[rev,k];counts['endpoint_checks']+=1
      counts['continuation_fixtures']+=1;counts['loop_fixtures']+=any(x==y for x,y,_ in edges)
 # Every three-type event matrix and grid pair of distributions, envelope cap V=2.
 probs=[a for a in product(range(5),repeat=3) if sum(a)==4]
 for P,Q in product(probs,repeat=2):
  tau4=sum(max(p-q,0) for p,q in zip(P,Q))
  for bits in product((0,1),repeat=6):
   for nu in product((0,1,3),repeat=2):
    h=[sum(nu[j]*bits[2*t+j] for j in range(2)) for t in range(3)]
    g=[min(2,v) for v in h];common=[min(p,q) for p,q in zip(P,Q)]
    assert sum(p*v for p,v in zip(P,g))<=sum(c*v for c,v in zip(common,h))+2*tau4
    assert sum(c*v for c,v in zip(common,h))<=sum(q*v for q,v in zip(Q,h))
    counts['common_part_checks']+=1
 # Per-type signed measures chosen after empirical P; event masks and envelopes fixed.
 for nu in product((1,2),repeat=2):
  family=[mu for mu in product(range(-2,3),repeat=2) if sum(map(abs,mu))<=2 and all(abs(mu[j])<=nu[j] for j in range(2))]
  for mu0,mu1 in product(family,repeat=2):
   for bits in product((0,1),repeat=4):
    w=[sum(abs(mu[j])*bits[2*t+j] for j in range(2)) for t,mu in enumerate((mu0,mu1))]
    h=[sum(nu[j]*bits[2*t+j] for j in range(2)) for t in range(2)]
    for a,b in product(range(5),repeat=2):
     assert a*w[0]+(4-a)*w[1]<=b*h[0]+(4-b)*h[1]+2*abs(a-b)
     counts['adaptive_measure_checks']+=1
 # Overlapping signed Auerbach vectors in a two-dimensional l1 subspace.
 u=(F(1,2),F(1,2));v=(F(1,2),F(-1,2));nu=tuple(abs(a)+abs(b) for a,b in zip(u,v))
 assert sum(nu)==2
 for a,b in product((F(j,4) for j in range(-8,9)),repeat=2):
  w=tuple(a*x+b*y for x,y in zip(u,v));norm=sum(map(abs,w));assert norm==max(abs(a),abs(b))
  assert all(abs(x)<=norm*z for x,z in zip(w,nu));counts['envelope_checks']+=1
 assert F(1,4)*min(2,100)==F(1,2) and F(1,4)*100==25
 diffuse=[]
 for N in (2,7,31,127):
  vec=[F((-1)**j,N) for j in range(N)];env=list(map(abs,vec));assert sum(env)==1
  diffuse.append(dict(support=N,dimension=1,envelope_mass='1',lost_l1_if_one_coordinate_kept=str(F(N-1,N))))
 budgets=[]
 for p in range(1,13):
  L=10*p;R=30*p;K=10*p*(R+1);B=300*p*p+150*p+5;V=1+4*p*B;delta=20*V+2
  theta=F(3,8)-F(2*p,4*L)-F(V,delta)-F(1,40)
  assert F(2*p*R+1,K)<=F(1,5) and theta>F(1,4) and theta-F(1,16)>F(3,16)
  assert F(delta,2*V)>10
  budgets.append(dict(p=p,theta=str(theta)))
 # A label quotient can change metric degree 2 into N+1; no such quotient is used.
 quotient=[]
 for N in (2,7,31):
  distances=lambda x,y:0 if x==y else (1 if x//2==y//2 else 3)
  assert all(distances(x,z)<=distances(x,y)+distances(y,z) for x,y,z in product(range(2*N),repeat=3))
  assert all(sum(distances(x,y)<=1 for y in range(2*N))==2 for x in range(2*N))
  quotient.append(dict(disjoint_pairs=N,original_closed_degree=2,degree_after_identifying_even_vertices=N+1))
 return dict(status='FINITE DIAGNOSTICS PASS; NOT A UNIVERSAL PROOF',counts=counts,diffuse=diffuse,budgets=budgets,quotient=quotient,discrepancy_example=dict(V=2,envelope_mass=100,tau='1/4',clipped_error='1/2',unclipped_error=25),scope='Toy incidence/state systems; not full F graphs and not proof/contribution certification')
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
