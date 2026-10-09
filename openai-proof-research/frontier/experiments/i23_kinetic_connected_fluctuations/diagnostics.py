"""Exact finite algebra checks; none certifies a continuum proof."""
from fractions import Fraction as F
from itertools import combinations
from math import factorial, comb, exp, sqrt
from pathlib import Path
import json
D=Path(__file__).resolve().parent

def connected(n,edges):
 parent=list(range(n))
 def find(a):
  while parent[a]!=a:a=parent[a]
  return a
 for a,b in edges:parent[find(a)]=find(b)
 return len({find(a) for a in range(n)})==1

def mst(n,edges):
 parent=list(range(n));out=[]
 def find(a):
  while parent[a]!=a:a=parent[a]
  return a
 for e in sorted(edges):
  a,b=e
  if find(a)!=find(b):parent[find(a)]=find(b);out.append(e)
 return tuple(out)

count=0;graph_sizes=[]
for n in range(1,6):
 all_e=list(combinations(range(n),2));graphs=[];trees=[]
 for mask in range(1<<len(all_e)):
  e=tuple(all_e[i] for i in range(len(all_e)) if mask>>i&1)
  if connected(n,e):
   graphs.append((mask,e))
   if len(e)==n-1:trees.append((mask,e))
 # MST interval identity: graphs of a given MST have all additional edges later than tree path maximum.
 intervals={e:[] for _,e in trees}
 for mask,e in graphs:intervals[mst(n,e)].append(mask)
 for tm,t in trees:
  qm=0
  for i,e in enumerate(all_e):
   if e not in t and mst(n,tuple(sorted(t+(e,))))==t:qm|=1<<i
  expected={tm|s for s in range(1<<len(all_e)) if s&~qm==0}
  assert set(intervals[t])==expected
 for a in range(1<<len(all_e)):
  ursell=sum((-1)**len(e) for mask,e in graphs if mask&~a==0)
  penrose=0;tree_bound=0
  for tm,t in trees:
   if tm&~a:continue
   tree_bound+=1
   qm=0
   for i,e in enumerate(all_e):
    if e not in t and mst(n,tuple(sorted(t+(e,))))==t:qm|=1<<i
   if not qm&a:penrose+=(-1)**(n-1)
  assert ursell==penrose and abs(ursell)<=tree_bound
  count+=1
 graph_sizes.append({'vertices':n,'connected_graphs':len(graphs),'spanning_trees':len(trees)})

factorial_checks=0
for p in range(1,81):
 for h in range(1,p+1):
  ratio=F(p**(2*(p-1)),factorial(p-1)*factorial(p-h))
  assert ratio<=9**p*p**(h-1)
  factorial_checks+=1

scalings=0
for p in range(1,101):
 for h in range(1,p+1):
  for links in range(p):
   assert -2*(p-h)+2*(p-1-links)+3*links==2*(h-1)+links
   scalings+=1
# Sparse residual: many labels can reroute although only two top roots exist.
rerouting=[]
for p in [3,5,10,100]:
 original=[(0,i) for i in range(2,p)]
 earlier=[(1,i) for i in range(2,p)]
 rerouting.append({'p':p,'h':2,'original_extra_pins':len(original),'changed_earliest_extra_pins':len(earlier)})

# phi=(r^-2-1)^4: exact -r phi'/phi=8/(1-r^2), and >=8.
virial=0
for den in range(2,81):
 for num in range(1,den):
  r=F(num,den);phi=(r**-2-1)**4;prime=4*(r**-2-1)**3*(-2*r**-3)
  assert -r*prime/phi==8/(1-r*r) and -r*prime>=8*phi
  virial+=1
# Rademacher Cox intensity: c2=eps^2, c4=-2eps^4; fluctuation cumulants k4=-2+o(1).
cox=[]
for eps in [F(1,2),F(1,4),F(1,16),F(1,64)]:
 c2=eps**2;c4=-2*eps**4
 # count cumulant k4=mu +7 mu^2 eps^2 + mu^4(-2eps^4), since third factorial cumulant zero.
 mu=eps**-2;ordinary4=(mu+7*mu**2*c2+mu**4*c4)/mu**2
 assert ordinary4==8*eps**2-2
 cox.append({'epsilon':str(eps),'normalized_c4':str(c4/eps**6),'ordinary_scaled_k4':str(ordinary4)})

# Exact majorant escape: eps=2^-n, a=log 2, p_n=2(h-1)n has mass eps^(2(h-1)).
escape=[]
for h in [2,3,4]:
 for n in [4,8,16]:
  eps=F(1,2**n);p=2*(h-1)*n;mass=F(1,2**p)
  assert mass==eps**(2*(h-1))
  escape.append({'h':h,'n':n,'p':p,'normalized_mass':1})
# Logarithmic tail / derivative-growth conflict of a proposed crude cutoff estimate.
cutoff=[]
for h in range(2,7):
 for a in range(1,5):
  for b in range(1,5):
   lower=F(2*(h-1),a);upper=F(1,b)
   cutoff.append({'h':h,'tail_a':a,'growth_b':b,'q_lower':str(lower),'q_upper':str(upper),'compatible':lower<upper})

out={'status':'PASS','scope':'Finite exact identities only; no continuum cumulant estimate certified',
'penrose_graph_checks':count,'graph_sizes':graph_sizes,'positive_component_factorial_checks':factorial_checks,'scaling_checks':scalings,'virial_rational_checks':virial,
'rerouting_graphs':rerouting,'cox_intensity_examples':cox,'normalized_tail_escape':escape,'cutoff_interval_checks':cutoff}
(D/'diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['cutoff_interval_checks','normalized_tail_escape']},indent=2))
