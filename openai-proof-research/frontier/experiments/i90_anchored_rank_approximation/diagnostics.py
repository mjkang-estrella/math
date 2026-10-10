#!/usr/bin/env python3
"""Read-only exact finite tests; no mathematical certification.
Permutation-incidence fixture adapted from sealed I88 diagnostics;
all statewise badness, signed-weight and discrepancy checks are new.
"""
import itertools,json
from fractions import Fraction as F

def run():
 cases=edges=loops=weighted=state_root_difference=0
 for nv in range(1,4):
  perms=list(itertools.permutations(range(nv)))
  for pp in itertools.product(perms,repeat=2):
   inc=[];out=[[] for _ in range(nv)]
   for perm in pp:
    for x,y in enumerate(perm):
     e=len(inc);inc += [(x,y,e+1),(y,x,e)];out[x].append(e);out[y].append(e+1)
   for bits in itertools.product((False,True),repeat=nv*2):
    for cross in (False,True):
     r={(e,j):0 for e in range(len(inc)) for j in range(2)}
     for n in range(1,5):
      old=r;r={}
      for e,(x,y,rev) in enumerate(inc):
       for j in range(2):
        r[e,j]=max([1+max(old[f,k] for f in out[y] if f!=rev) for k in range(2) if bits[2*x+j] and bits[2*y+k] and (j==k or cross)],default=0)
      if n<2:continue
      bad={(x,j):any(r[e,j]==n for e in out[x]) for x in range(nv) for j in range(2)}
      def exceptional(e,j):
       x=inc[e][0];return bad[x,j] or all(r[e,j]>r[f,j] for f in out[x] if f!=e)
      for x in range(nv):
       state_root_difference += bad[x,0]!=bad[x,1]
       for j in range(2):
        if not bad[x,j]:assert sum(exceptional(e,j) for e in out[x])<=1
       for mu in [(F(1),F(0)),(F(3,2),F(-1,2)),(F(-2),F(3))]:
        tv=sum(map(abs,mu));bm=sum(abs(mu[j])*bad[x,j] for j in range(2))
        avg=sum(sum(abs(mu[j])*exceptional(e,j) for j in range(2)) for e in out[x])/4
        assert avg<=tv/4+bm;weighted+=1
      for e,(x,y,rev) in enumerate(inc):
       for j,k in itertools.product(range(2),repeat=2):
        if bits[2*x+j] and bits[2*y+k] and (j==k or cross):assert exceptional(e,j) or exceptional(rev,k);edges+=1
      cases+=1;loops+=any(x==y for x,y,_ in inc)
 # Exact bounded-observable total-variation transfer for three local types.
 probs=[tuple(F(i,4) for i in a) for a in itertools.product(range(5),repeat=3) if sum(a)==4]
 clipped=0
 for P,Q in itertools.product(probs,repeat=2):
  tau=sum(abs(x-y) for x,y in zip(P,Q))/2
  for masses in itertools.product((F(0),F(1,2),F(2),F(100)),repeat=3):
   g=[min(F(2),v) for v in masses]
   assert sum(p*x for p,x in zip(P,g))<=sum(q*x for q,x in zip(Q,g))+2*tau
   clipped+=1
 # Exhaustive colors on radius-n degree-two tree; fixed metric states, no relabeling.
 rare=0
 for n in range(1,4):
  for cross in (False,True):
   Q=2 if cross else 1
   for labels in itertools.product(range(3),repeat=2):
    counts=[0,0]
    for colors in itertools.product(range(3),repeat=1+2*n):
     for j in range(2):
      hit=False
      for path in ([0]+list(range(1,n+1)),[0]+list(range(n+1,2*n+1))):
       states={j} if colors[0]==labels[j] else set()
       for v in path[1:]:states={k for h in states for k in range(2) if (h==k or cross) and colors[v]==labels[k]}
       hit |= bool(states)
      counts[j]+=hit
    for count in counts:
     assert F(count,3**(1+2*n))<=F(2**n*Q**n,3**(n+1));rare+=1
 constants=[]
 for p in range(1,9):
  L,R=10*p,30*p;K=10*p*(R+1);D=K+2*L+5;B=4*R+D;V=1+4*p*B;delta=20*V+2
  theta=F(3,8)-F(2*p,4*L)-F(V,delta)-F(1,40)
  assert theta>F(1,4) and theta-F(1,16)>F(3,16)
  # k/(4VH)>delta*Q/(2V)>10: valid for every allowed k.
  assert F(delta,2*V)>10
  constants.append(dict(p=p,V=V,delta=delta,theta=str(theta)))
 # A diffuse one-dimensional envelope has bounded mass independent of support.
 diffuse=[]
 for N in (2,8,64,256):
  w=[F((-1)**i,N) for i in range(N)];env=[abs(x) for x in w]
  assert sum(env)==1
  for c in (F(-3),F(-1,2),F(0),F(2)):assert all(abs(c*x)<=3*e for x,e in zip(w,env))
  diffuse.append(dict(support=N,envelope_mass='1'))
 return dict(status='PASS_FINITE_STRESS_TESTS_ONLY',pair_continuation_cases=cases,compatible_edge_state_checks=edges,cases_with_loops=loops,statewise_vs_rootwise_examples=state_root_difference,signed_weighted_average_checks=weighted,clipped_tv_checks=clipped,tree_color_bounds=rare,constants=constants,diffuse=diffuse)
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
