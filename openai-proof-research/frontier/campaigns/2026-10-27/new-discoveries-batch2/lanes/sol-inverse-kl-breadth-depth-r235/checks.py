from pathlib import Path
from math import comb
from functools import lru_cache
from fractions import Fraction
import json
L=Path(__file__).resolve().parent
def cat(k):return comb(2*k,k)//(k+1)
def separated(s,n):return not (s&(((s<<1)|(s>>(n-1)))&((1<<n)-1)))
def weights(n):
 ss=[s for s in range(1<<n) if separated(s,n)]
 w={s:cat(n-s.bit_count()-2) for s in ss}
 for i in range(n):
  for s in ss:
   if not s>>i&1 and s|1<<i in w:w[s]-=w[s|1<<i]
 return {s:a for s,a in w.items() if a}
@lru_cache(None)
def triang(v):
 if len(v)<3:return (frozenset(),)
 ans=[]
 for j in range(1,len(v)-1):
  for a in triang(v[:j+1]):
   for b in triang(v[j:]):
    edges=set(a|b)
    for x,y in [(v[0],v[j]),(v[j],v[-1])]:
     if y-x>1:edges.add((x,y))
    ans.append(frozenset(edges))
 return tuple(ans)
def clique(vertices):
 # Exhaustive include/exclude recursion, at most n=13 orbit vertices.
 if not vertices:return []
 v=vertices[0];a=clique([u for u in vertices[1:] if u&v]);a=[v]+a
 b=clique(vertices[1:]) if len(vertices)-1>len(a) else []
 return max(a,b,key=len)
out={'rank19_coefficients':[163,1790,10323,39217,106659,215169,323646,350404,232662,71162]}
a=out['rank19_coefficients'];out['rank19_defects']=[a[i]**2-a[i-1]*a[i+1] for i in range(1,len(a)-1)];assert min(out['rank19_defects'])>0
start=[34705212702720,475418034176,609014784,89280]
for j in range(64):start[0]-=2**36;start[1]+=-2**36+(504-j)*2**28
assert start==[30307166191616,4194859712512,609014784,89280]
out['public_counterexample']={'coefficients':start,'delta2':start[2]**2-start[1]*start[3]};assert out['public_counterexample']['delta2']==-3618068002504704
out['ear_checks']=[];out['orbit_obstructions']=[]
for n in range(5,14):
 w=weights(n);assert sum(w.values())==cat(n-2)
 stars=[sum(a for s,a in w.items() if s>>i&1) for i in range(n)];assert set(stars)=={cat(n-3)}
 row={'n':n,'patterns':len(w),'total':sum(w.values()),'star':stars[0]}
 if n<=10:
  literal={}
  for t in triang(tuple(range(n))):
   t=set(t)-{(0,n-1)}
   s=sum(1<<i for i in range(n) if tuple(sorted(((i-1)%n,(i+1)%n))) in t)
   literal[s]=literal.get(s,0)+1
  assert literal==w;row['literal_triangulations_verified']=sum(literal.values())
 # Check proposed orbit-by-orbit cyclic averaging bound.
 seen=set()
 for s in w:
  if s in seen:continue
  orb=sorted({((s<<i)|(s>>(n-i)))&((1<<n)-1) for i in range(n)});seen.update(orb)
  c=clique(orb)
  if n*len(c)>s.bit_count()*len(orb):
   out['orbit_obstructions'].append({'n':n,'pattern':s,'orbit_size':len(orb),'size':s.bit_count(),'clique':c,'exact_weight':w[s],'star_orbit_count':Fraction(s.bit_count()*len(orb),n).__str__()});break
 out['ear_checks'].append(row)
out['pentagon_fractional_obstruction']={'patterns':list(weights(5)),'all_weights':list(weights(5).values()),'fractional_value':'5/2','star':2,'reason':'Every pairwise-disjoint collection has size <=2; assign 1/2 to all five patterns. Integral intersecting maximum is 2.'}
(L/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
