import sys,itertools as it,time,json,hashlib
from pathlib import Path
D=Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'vendor'))
import networkx as nx
comp=lambda s: ''.join('1' if c=='0' else '0' for c in s)
for d in range(12,13):
 start=time.monotonic();groups={};count=0;potential=[]
 for k in range(3,d):
  for bits in it.product('01',repeat=k):
   f=''.join(bits)
   if f!=min(f,f[::-1],comp(f),comp(f[::-1])):continue
   vs=[x for x in range(2**d) if f not in format(x,f'0{d}b')];V=set(vs)
   g=nx.Graph();g.add_nodes_from(vs);g.add_edges_from((x,x^(1<<i)) for x in vs for i in range(d) if x^(1<<i) in V)
   nu=sum(a!=b for a,b in zip(f,f[1:]));count+=1
   key=(len(g),g.number_of_edges(),nx.weisfeiler_lehman_graph_hash(g,iterations=5))
   for old,n in groups.get(key,[]):
    if nu!=n:potential.append([old,f,n,nu])
   groups.setdefault(key,[]).append((f,nu))
 print(json.dumps(dict(d=d,representatives=count,cross_index_invariant_collisions=len(potential),collision_examples=potential[:15],no_collisions_implies_no_isomorphisms=True,diagnostic_hash_trust='NetworkX invariant, not kernel proof',seconds=time.monotonic()-start)),flush=True)
