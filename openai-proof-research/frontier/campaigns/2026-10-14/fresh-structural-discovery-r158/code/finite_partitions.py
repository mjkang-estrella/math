from fractions import Fraction as F
from itertools import product
from collections import Counter
from pathlib import Path
import json
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r158')
S=[(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]
def vec(j,t,sign): return tuple((1+F(sign)*t*s[j])/4 for s in S)
def stats(law):
 m=h=F(0)
 for p,w in law:
  x=[sum(p[g]*S[g][j] for g in range(4)) for j in range(3)]
  m+=w*sum(z*z for z in x); h+=w*x[0]*x[1]*x[2]
 return m,h
def prod(mu,nu):
 out=[]
 for p,w in mu:
  for q,z in nu:
   c=[4*p[i]*q[i] for i in range(4)]; Z=sum(c)
   if Z: out.append((tuple(x/Z for x in c),w*z*Z))
 assert sum(w for _,w in out)==1
 return out
def axis(j,t): return [(vec(j,t,s),F(1,2)) for s in [-1,1]]
rows=[]
for a,b in product([F(1,5),F(1,2),F(1)],repeat=2):
 same=stats(prod(axis(0,a),axis(0,b)))[0]; diff=stats(prod(axis(0,a),axis(1,b)))[0]
 expected=F(1) if a*b==1 else (a*a+b*b-2*a*a*b*b)/(1-a*a*b*b)
 assert same==expected and diff==a*a+b*b+a*a*b*b
 rows.append({'a':str(a),'b':str(b),'same_m':str(same),'different_m':str(diff),'random_axes_m':str((same+2*diff)/3)})
# Exact four-state transition after randomized observed partition and compatible-state sampling.
Q=[[sum(F(1,6) for j in range(3) if S[g][j]==S[h][j]) for h in range(4)] for g in range(4)]
assert Q==[[F(1,2) if g==h else F(1,6) for h in range(4)] for g in range(4)]
# Four leaves, two binary branch vertices; rational edge parameter 1/2 throughout.
lam=F(1,2); P=[[lam*(g==h)+(1-lam)/4 for h in range(4)] for g in range(4)]
def info(mark):
 m=tv=F(0)
 for obs in product([-1,1],repeat=4):
  branch=[]
  for k in range(2):
   ell=[]
   for g in range(4):
    v=F(1)
    for leaf in [2*k,2*k+1]: v*=sum(P[g][h] for h in range(4) if S[h][mark[leaf]]==obs[leaf])
    ell.append(v)
   branch.append([sum(P[g][h]*ell[h] for h in range(4)) for g in range(4)])
  lik=[branch[0][g]*branch[1][g] for g in range(4)]; Z=sum(lik)/4
  if Z:
   p=[v/(4*Z) for v in lik]; m+=Z*(4*sum(x*x for x in p)-1); tv+=Z*sum(abs(x-F(1,4)) for x in p)/2
 return m,tv
hist=Counter(); allrows=[]
for mark in product(range(3),repeat=4):
 m,tv=info(mark); hist[(str(m),str(tv))]+=1; allrows.append({'mark':mark,'m':str(m),'advantage':str(tv)})
# Integer definition of floor(3/4 log2(k+1)), without floating point.
stages=[]
for k in range(1,65):
 d=((k+1)**3).bit_length()-1; q=d//4; N=2**(k+q)
 oldq=((k**3).bit_length()-1)//4; degree=2**(1+q-oldq); assert degree in [2,4]
 stages.append({'stage':k,'extra_exponent':q,'children':degree,'vertices':N,'unit_flow_p3_term':str(F(3,4)*F(1,2**q)**2),'unit_flow_p2_term':str(F(1,2**q)),'mono_probability':'3^(1-'+str(N)+')','plateau_length':str(k*k)+'*3^'+str(N)})
out={'scope':'exact finite identities; not infinite reconstruction or novelty certification','two_input_rows':rows,'random_partition_channel':[[str(x) for x in row] for row in Q],'four_leaf_histogram':[{'m':a,'advantage':b,'count':c} for (a,b),c in sorted(hist.items())],'four_leaf_all_markings':allrows,'first_64_core_stages':stages}
(R/'receipts/finite-partitions.json').write_text(json.dumps(out,indent=2)); print('9 pair identities;81 four-leaf assignments;64 core stages; no expanded infinite tree instantiated'); print(out['four_leaf_histogram'])
