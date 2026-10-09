"""Exact finite diagnostics; the universal proofs are in the I37 report."""
from fractions import Fraction as F
from itertools import product,combinations
import json

def trees(maxnodes=10):
 by={1:[()]}
 for size in range(2,maxnodes+1):
  arr=[]
  for degree in range(2,5):
   for sizes in product(range(1,size),repeat=degree):
    if sum(sizes)!=size-1 or any(not by.get(s) for s in sizes):continue
    arr.extend(product(*(by[s] for s in sizes)))
  by[size]=arr
 return [t for ts in by.values() for t in ts]
def q(t):
 return F(1) if not t else sum((F(1,2**(i+1))*q(c) for i,c in enumerate(t[:-1])),F(0))
def badnodes(t,path=()):
 if not t:return []
 ans=[path] if t[-2] else []
 for i,c in enumerate(t[:-1]):ans+=badnodes(c,path+(i,))
 return ans
def assign(t):
 cursor=3; serial=0; data={}
 def visit(node,path=()):
  nonlocal cursor,serial
  for i,c in enumerate(node):
   serial+=1; r=1+serial%3; a=cursor;b=a+r-1;cursor=b+1+serial%2
   e=path+(i,); data[e]=[a,b,None]
   visit(c,e)
   data[e][2]=max(v[1] for k,v in data.items() if k[:len(e)]==e)
 visit(t);return data
def at(t,path):
 for i in path:t=t[i]
 return t
def rooted_star(E,N):
 for x in E:
  witnesses=[]
  for i in range(N):
   shift=N-1-i; prefix=x>>(shift+1);bit=(x>>shift)&1
   w=next((y for y in E if y>>(shift+1)==prefix and ((y>>shift)&1)!=bit),None)
   if w is None:break
   witnesses.append(w)
  if len(witnesses)==N:return x,witnesses
 return None
def main():
 ts=trees(); bad=0; nobad=0; bounds=0
 for t in ts:
  bs=badnodes(t)
  if not bs: assert q(t)>=F(1,2);nobad+=1
  else:bad+=1
  if q(t)<F(1,2):assert bs
  data=assign(t)
  for path in bs:
   node=at(t,path);T=sum(data[path+(i,)][1]-data[path+(i,)][0]+1 for i in range(len(node)-1))
   a,b,B=data[path+(len(node)-2,)];D=B*B-a*a
   assert b>=T and B>=b+2 and D>=4*T+4
   # Integer lower bound suffices for ALL 0<p<1, without float exponentials.
   assert D-T>0;bounds+=1
 stars=[]
 for N in range(1,5):
  size=1<<N;maxbad=0;counter=0
  for mask in range(1<<size):
   E={i for i in range(size) if (mask>>i)&1};w=rooted_star(E,N)
   if w is None:maxbad=max(maxbad,len(E))
   if len(E)>size//2:assert w is not None
   counter+=1
  assert maxbad==size//2
  stars.append(dict(N=N,subsets=counter,maximum_star_free=maxbad))
 # Exact finite digital-cover problem K=4,N=2.
 K=4;N=2;Q=1<<K
 edges=set()
 for j in range(Q):
  for h in range(Q+1):
   edges.add(tuple(sorted({(j+(1<<(K-n*n))+(h>>(n*n)))%Q for n in range(1,N+1)})))
 maxE=0;witness=None
 for mask in range(1<<Q):
  if mask.bit_count()<=maxE:continue
  if all(not all((mask>>v)&1 for v in edge) for edge in edges):maxE=mask.bit_count();witness=mask
 assert maxE==2
 # Continuous-to-digital enclosure, including endpoints and wrap-around.
 enclosure=0
 for K,N in [(4,2),(9,3)]:
  Q=1<<K
  for j,h,u,v in product([0,1,Q//2,Q-1],[0,1,Q//2,Q-1], [F(0),F(1,3),F(999,1000)],[F(0),F(1,7),F(999,1000)]):
   x=(j+u)/Q;t=1+(h+v)/Q
   for n in range(1,N+1):
    z=Q*(x+t/F(2**(n*n)));cell=z.numerator//z.denominator
    base=j+(1<<(K-n*n))+(h>>(n*n))
    assert cell-base in [0,1];enclosure+=1
 # Actual periodic keys and a completion separating two local predicates.
 # Root's first child is internal, with two leaves; its second leaf is default.
 fixture=(((),()),()); data=assign(fixture);a,b,B=data[(0,)];ell=2
 def key(z,idx):
  qgrid=2**(idx*idx+ell);fr=z-(z.numerator//z.denominator)
  return (qgrid*fr).numerator//(qgrid*fr).denominator
 signature_pairs=0
 scales=[F(1),F(3,2),F(2),F(1)+F(1,2**(B*B+ell-a*a)),F(1)+F(1,2**(B*B+ell-a*a+1))]
 for x in [F(0),F(1,3),F(1023,1024)]:
  lo=2**(B*B+ell)*(x+F(1,2**(a*a)));hi=2**(B*B+ell)*(x+F(2,2**(a*a)))
  assert (hi.numerator//hi.denominator)-(lo.numerator//lo.denominator)==2**(B*B+ell-a*a)
  for t,u in combinations(scales,2):
   y=x+t/F(2**(a*a));z=x+u/F(2**(a*a))
   if key(y,B)==key(z,B):continue
   selectors={('root',key(x,b)):0,('child',key(x,data[(0,0)][1])):1}
   for point in [y,z]:
    for table,idx,value in [('root',b,1),('child',data[(0,0)][1],0)]:
     address=(table,key(point,idx));assert address not in selectors or selectors[address]==value;selectors[address]=value
   terminal={key(y,B):1,key(z,B):0}
   for point,value in [(y,1),(z,0)]:
    assert selectors['root',key(point,b)]==1
    assert selectors['child',key(point,data[(0,0)][1])]==0
    assert terminal[key(point,B)]==value
   signature_pairs+=1
 # Exact stopping recursion for biased combs.
 combcases=0
 for c,A,d in product([F(1,3),F(99,100)],[F(1,4),F(99,100)],range(1,9)):
  value=F(1)
  for _ in range(d):value=c*value+(1-c)*(1-A)
  assert value==1-A+A*c**d;combcases+=1
 # Bound normalized finite gaps for arbitrary square-index subsets.
 gapcases=0
 for m in range(3,7):
  for ns in combinations(range(1,11),m):
   a=[F(1,2**(n*n)) for n in ns]
   delta=min(a[i]-a[i+1] for i in range(m-1))/(a[0]-a[-1])
   upper=F(8,7)*F(1,2**((m-1)**2-1))
   assert delta<=upper;gapcases+=1
 # Biased independent selectors: exhaustive probability of failed tests.
 probability_cases=0
 for theta in [(F(1,3),F(2,5)),(F(1,100),F(99,100)),(F(1,2),)*3]:
  for p in [F(1,100),F(1,4),F(3,4)]:
   actual=F(0)
   for bits in product([0,1],repeat=len(theta)):
    weight=F(1)
    for th,a in zip(theta,bits):weight*=th if a else 1-th
    actual+=weight*(1-p)**sum(bits)
   expected=F(1)
   for th in theta:expected*=1-p*th
   assert actual==expected;probability_cases+=1
 assert 5**2-1**2==7**2-5**2==24
 blocking=16-maxE
 assert blocking==14
 return dict(ordered_trees=len(ts),trees_with_signature_obstruction=bad,trees_without_obstruction=nobad,nonuniform_local_bounds=bounds,actual_key_separating_completions=signature_pairs,biased_comb_cases=combcases,rooted_star_exhaustion=stars,digital_cover=dict(K=4,N=2,distinct_edges=len(edges),max_avoiding_cells=maxE,min_blocking_cells=blocking,witness_complement_mask=witness),continuous_enclosures=enclosure,relative_gap_cases=gapcases,biased_probability_cases=probability_cases,square_difference_collision=24)
if __name__=='__main__':print(json.dumps(main(),indent=2)+'\n',end='')
