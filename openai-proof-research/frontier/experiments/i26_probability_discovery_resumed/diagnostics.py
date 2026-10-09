"""Deterministic exact finite diagnostics; no scaling theorem is inferred."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from collections import defaultdict
import json, math
R=Path(__file__).resolve().parents[3]
OUT=R/'frontier/experiments/i26_probability_discovery_resumed/diagnostics.json'
STEPS=((1,0),(0,1),(1,-1),(-1,0),(0,-1),(-1,1))
def graph(r):
 V=sorted((i,j) for i in range(-r,r+1) for j in range(-r,r+1) if max(abs(i),abs(j),abs(i+j))<=r)
 adj={v:sorted((v[0]+a,v[1]+b) for a,b in STEPS if (v[0]+a,v[1]+b) in V) for v in V}
 boundary=sorted((v for v in V if max(abs(v[0]),abs(v[1]),abs(sum(v)))==r),key=lambda v:math.atan2(math.sqrt(3)*v[1],2*v[0]+v[1]))
 triangles=[t for t in combinations(V,3) if all(b in adj[a] for a,b in combinations(t,2))]
 et=defaultdict(list)
 for i,t in enumerate(triangles):
  for e in combinations(t,2):et[e].append(i)
 return V,adj,boundary,triangles,et
def enumerate_heights(V,adj,pins):
 # Boundary is pinned, so finite domains are bounded by graph distance.
 dist={v:0 for v in pins};queue=list(pins)
 for v in queue:
  for w in adj[v]:
   if w not in dist:dist[w]=dist[v]+1;queue.append(w)
 h=dict(pins);out=[]
 def rec():
  if len(h)==len(V):out.append(tuple(h[v] for v in V));return
  options=[]
  for v in V:
   if v in h:continue
   lo=-1-2*dist[v];hi=1+2*dist[v]
   for w in adj[v]:
    if w in h:lo=max(lo,h[w]-2);hi=min(hi,h[w]+2)
   vals=list(range(lo,hi+1,2));options.append((len(vals),v,vals))
  _,v,vals=min(options)
  for x in vals:h[v]=x;rec()
  h.pop(v,None)
 rec();return out
def trace(V,boundary,triangles,et,h):
 d=dict(zip(V,h));be=[tuple(sorted((boundary[i],boundary[(i+1)%len(boundary)]))) for i in range(len(boundary)) if d[boundary[i]]*d[boundary[(i+1)%len(boundary)]]<0]
 assert len(be)==2
 edge=min(be);prev=None;path=[];pins={}
 while True:
  nxt=[i for i in et[edge] if i!=prev]
  if not nxt:break
  assert len(nxt)==1
  t=nxt[0];assert t not in [record[0] for record in path]
  for v in triangles[t]:assert abs(d[v])==1;pins[v]=d[v]
  exits=[e for e in combinations(triangles[t],2) if d[e[0]]*d[e[1]]<0 and e!=edge]
  assert len(exits)==1
  edge=exits[0];path.append((t,edge));prev=t
 return tuple(path),pins
counts=defaultdict(int);examples=[];nonharmonic=None
for radius in (1,2):
 V,adj,boundary,triangles,et=graph(radius)
 # Every arc length, at each boundary start: 30 + 132 ordered experiments.
 for start in range(len(boundary)):
  for length in range(1,len(boundary)):
   plus={boundary[(start+j)%len(boundary)] for j in range(length)}
   boundary_pins={v:1 if v in plus else -1 for v in boundary}
   hs=enumerate_heights(V,adj,boundary_pins);assert hs
   counts['boundary_experiments']+=1;counts['height_configurations']+=len(hs)
   groups=defaultdict(list);prefixes={}
   for h in hs:
    path,pins=trace(V,boundary,triangles,et,h);groups[path].append(h)
    for k in range(len(path)+1):
     key=path[:k];pp=dict(boundary_pins)
     for t,exit_edge in key:
      for v in triangles[t]:pp[v]=h[V.index(v)]
     if key in prefixes:assert prefixes[key]==pp
     prefixes[key]=pp
   # Complete conditioning gives an independent product of constant-boundary laws.
   terminal_projection={}
   for path,gh in groups.items():
    pins=prefixes[path];free=set(V)-set(pins);components=[]
    while free:
     c={min(free)};stack=list(c)
     for v in stack:
      for w in adj[v]:
       if w in free and w not in c:c.add(w);stack.append(w)
     free-=c;components.append(sorted(c))
    signs=dict(pins);product=1
    for c in components:
     labels={pins[w] for v in c for w in adj[v] if w in pins};assert len(labels)==1
     sign=next(iter(labels));signs.update({v:sign for v in c})
     projections={tuple(h[V.index(v)] for v in c) for h in gh};product*=len(projections)
     for v in c:assert sum(h[V.index(v)] for h in gh)==sign*len(gh);counts['terminal_mean_identities']+=1
    assert product==len(gh);counts['terminal_product_checks']+=1
    terminal_projection[path]=tuple(signs[v] for v in V)
   # Exact pinned completion identity and Doob projection/tower formula at all prefixes.
   for prefix,pins in prefixes.items():
    matching=[h for h in hs if all(h[V.index(v)]==x for v,x in pins.items())]
    traced=[h for path,gh in groups.items() if path[:len(prefix)]==prefix for h in gh]
    assert set(matching)==set(traced);counts['prefix_pin_identities']+=1
    for i,v in enumerate(V):
     rhs=sum(len(gh)*terminal_projection[path][i] for path,gh in groups.items() if path[:len(prefix)]==prefix)
     assert sum(h[i] for h in matching)==rhs
     assert abs(rhs)<=len(matching);counts['bounded_martingale_identities']+=1
   if radius==1 and start==0 and length==1:
    center=V.index((0,0));m=F(sum(h[center] for h in hs),len(hs));harm=F(sum(boundary_pins.values()),6)
    assert m!=harm;nonharmonic={'boundary_plus':list(plus),'mean':str(m),'discrete_harmonic_center':str(harm),'configurations':len(hs)}
   if radius==2 and start==0 and length in (1,6,11):examples.append(dict(radius=radius,plus_length=length,configurations=len(hs),paths=len(groups),prefixes=len(prefixes)))
# Exact logical countermodel: deterministic coordinate tests versus adaptive coordinate.
adaptive=[]
for n in (4,8,16,32,64,128):
 # Uniform J in {0,...,n-1}; X_j = 1_{J=j}. Every fixed test error is 1/n,
 # selected test X_J = 1. Even boundedness/UI does not interchange sup and limit.
 means=[sum(F(int(j==k),n) for j in range(n)) for k in range(n)]
 assert max(means)==F(1,n)
 adaptive.append({'n':n,'fixed_error':str(max(means)),'adaptive_error':1})
# Ito/Hadamard coefficients, rational after removing pi and sigma factors.
# m=a-b arg Z, b=2l/pi. Bracket coefficient b^2*kappa;
# -dG=(2/pi) Im(1/Z)Im(1/W)dt. At kappa=4 gives sigma^2=8l^2/pi.
ito=[]
for kappa in range(1,9):
 drift=F(4-kappa,2);bracket=4*kappa
 assert (drift==0)==(kappa==4)
 ito.append({'kappa':kappa,'Im_inverse_square_drift':str(drift),'bracket_times_pi_squared_over_l_squared':bracket})
# Ising moment obstruction: mean one and second moment ~L^1/4, but log/ sqrt(log L) ->0.
ising=[]
for m in (2,3,4,8,16,32):
 p=F(1,m);a=F(1,2);b=F(m+1,2)
 assert (1-p)*a+p*b==1
 second=(1-p)*a*a+p*b*b
 assert second==F(m+3,4)
 ising.append({'m':m,'prob_rare':str(p),'second_moment':str(second),'L':m**4})
result={'status':'PASS','counts':dict(counts),'examples':examples,'finite_nonharmonic_counterexample':nonharmonic,'adaptive_test_countermodel':adaptive,'ito_normalization':ito,'ising_second_moment_countermodel':ising,'limits':'Exact finite checks and abstract countermodels; no interface tightness, uniform slit convergence, or CLT is certified.'}
OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
