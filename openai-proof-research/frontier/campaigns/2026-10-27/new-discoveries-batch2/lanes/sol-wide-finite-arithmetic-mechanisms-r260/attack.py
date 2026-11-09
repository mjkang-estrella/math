from work import *
import itertools, numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog
from scipy.spatial import ConvexHull
from fractions import Fraction as F
n=4; edges=list(itertools.combinations(range(n),2)); perms=list(itertools.permutations(range(n)))
states=list(itertools.product(range(3),repeat=6)); sid={s:i for i,s in enumerate(states)}
def image(s,p):
 d={}
 for (i,j),v in zip(edges,s):
  a,b=p[i],p[j];d[min(a,b),max(a,b)]=v if a<b else 2-v
 return tuple(d[e] for e in edges)
keys={}; var={}
for s in states:
 for i in range(n):
  key=min((image(s,p),p[i]) for p in perms)
  if key not in keys:keys[key]=len(keys)
  var[s,i]=keys[key]
N=len(keys)
eq=[];ub=[]
for s in states:
 row={}
 for i in range(n):row[var[s,i]]=row.get(var[s,i],0)+1
 eq.append(row)
 for e,(i,j) in enumerate(edges):
  if s[e]==2:continue
  t=list(s);t[e]+=1;t=tuple(t)
  for a,sgn in [(i,1),(j,-1)]:
   row={}
   for v,c in [(var[s,a],sgn),(var[t,a],-sgn)]:row[v]=row.get(v,0)+c
   ub.append(row)
def sparse(rows):
 rr=[];cc=[];dd=[]
 for i,row in enumerate(rows):
  for j,c in row.items():
   if c:rr.append(i);cc.append(j);dd.append(c)
 return coo_matrix((dd,(rr,cc)),shape=(len(rows),N)).tocsr()
Aeq=sparse(eq);Aub=sparse(ub)
opts=[]
for i in range(n):opts.append([(i,i),(0,0)]+list(itertools.combinations(range(i+1),2)))
verts=[]
for arcs in itertools.product(*opts):
 v=[0]*n
 for a,b in arcs:v[a]+=1;v[b]+=1
 verts.append(v)
verts=np.unique(np.array(verts),axis=0);hull=ConvexHull(verts[:,:3])
# Integral supporting planes, validated against every generating vector.
planes=set()
for row in hull.equations:
 fs=[F(float(x)).limit_denominator(1000) for x in row]
 # recover integer ratios from first nonzero normal
 base=next(x for x in row[:3] if abs(x)>1e-8)
 fs=[F(float(x/base)).limit_denominator(100) for x in row]
 import math,functools
 den=functools.reduce(math.lcm,[x.denominator for x in fs],1)
 a=tuple(int(x*den) for x in fs)
 if base<0:a=tuple(-x for x in a)
 assert all(sum(a[j]*int(v[j]) for j in range(3))+a[3]<=0 for v in verts)
 planes.add(a)
Ds=[]
for s in states:
 P=[[1]*n for _ in range(n)]
 for (i,j),v in zip(edges,s):P[i][j]=v;P[j][i]=2-v
 if all(P[i][j]>=P[i+1][j] for i in range(n-1) for j in range(n)):Ds.append(s)
out=[]
for s in Ds:
 for plane in sorted(planes):
  obj=np.zeros(N)
  for i in range(3):obj[var[s,i]]-=plane[i]
  r=linprog(obj,A_ub=Aub,b_ub=np.zeros(len(ub)),A_eq=Aeq,b_eq=np.ones(len(eq)),bounds=(0,None),method='highs',options={'threads':1})
  assert r.success
  # Rational primal feasibility and exact facet value; numerical optimality alone is not proof.
  x=[F(float(z)).limit_denominator(100000) for z in r.x]
  assert all(sum(c*x[j] for j,c in row.items())==1 for row in eq)
  assert all(sum(c*x[j] for j,c in row.items())<=0 for row in ub)
  value=sum(F(plane[i])*x[var[s,i]] for i in range(3))+F(plane[3],8)
  # Exact rational dual upper bound for minimization (nonnegative primal).
  y=[F(float(z)).limit_denominator(100000) for z in r.eqlin.marginals]
  z=[F(float(z)).limit_denominator(100000) for z in r.ineqlin.marginals]
  coeff=[F(0)]*N
  for rows,weights in [(eq,y),(ub,z)]:
   for row,w in zip(rows,weights):
    for j,c in row.items():coeff[j]+=c*w
  assert all(w<=0 for w in z)
  assert all(coeff[j]<=F(float(obj[j])) for j in range(N))
  upper=-sum(y)+F(plane[3],8)
  if value>0:
   witness={'state':s,'plane':plane,'win_vector':[str(x[var[s,i]]) for i in range(n)],'grid_values':[[str(x[var[t,i]]) for i in range(n)] for t in states],'states':states,'slack':str(value)}
   (L/'witness-last.json').write_text(json.dumps(witness,indent=2))
   if plane==(-1,-1,0,4) and value==F(1,4):(L/'witness-best.json').write_text(json.dumps(witness,indent=2))
  out.append({'state':s,'plane':plane,'exact_primal_slack':str(value),'exact_dual_upper_slack':str(upper)})
print('variables',N,'D states',len(Ds),'facets',len(planes),'LPs',len(out),'max',max(F(x['exact_dual_upper_slack']) for x in out))
(L/'exact-checks.json').write_text(json.dumps({'scope':'n4, coordinate grid {0,1/2,1}; NOT all order types, NOT universal conjecture','variables':N,'D_states':len(Ds),'facet_normals':sorted(planes),'exact_rational_primal_dual_checks':out},indent=2))
