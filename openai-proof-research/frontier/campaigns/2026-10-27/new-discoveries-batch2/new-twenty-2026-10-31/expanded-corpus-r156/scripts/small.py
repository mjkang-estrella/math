import itertools,json,time
from pathlib import Path
out={}
# Wang k=1, all loopless labelled digraphs on 3,4 vertices.
rows=[]
for n in [3,4]:
 arcs=list(itertools.permutations(range(n),2));tested=0
 for mask in range(1<<len(arcs)):
  A={arcs[i] for i in range(len(arcs)) if mask>>i&1}
  if min(min(sum((v,w) in A for w in range(n)),sum((w,v) in A for w in range(n))) for v in range(n))<2:continue
  tested+=1
  assert any(all((p[i],p[(i+1)%len(p)]) in A for i in range(len(p))) for k in range(3,n+1) for p in itertools.permutations(range(n),k))
 rows.append({'n':n,'all_digraphs':1<<len(arcs),'semidegree_at_least_two_tested':tested})
out['345350']=rows
# Hefetz: every orientation of K4 and octahedron, plus wheel with five rim vertices.
rows=[]
for name,n,E in [('K4',4,list(itertools.combinations(range(4),2))),('octahedron',6,[(a,b) for a,b in itertools.combinations(range(6),2) if a//2!=b//2]),('wheel6',6,[(i,(i+1)%5) for i in range(5)]+[(i,5) for i in range(5)])]:
 target=(3*n+4)//5;worst=n;tested=0
 for mask in range(1<<len(E)):
  A={(a,b) if mask>>j&1 else (b,a) for j,(a,b) in enumerate(E)}
  def acyclic(S):
   S=set(S)
   while S:
    zero={v for v in S if not any((w,v) in A for w in S)}
    if not zero:return False
    S-=zero
   return True
  assert any(acyclic(S) for S in itertools.combinations(range(n),target));tested+=1
 rows.append({'underlying_planar_graph':name,'n':n,'orientations_exhausted':tested,'acyclic_size_required':target})
out['327034']=rows
# Lattice point-centered truncated balls in dimension3 radius2: cyclic quotients order19.
ball=[v for v in itertools.product([-1,0,1],repeat=3) if sum(x!=0 for x in v)<=2];N=len(ball);tested=0;witness=[]
for a in itertools.product(range(N),repeat=3):
 tested+=1
 if len({sum(x*y for x,y in zip(v,a))%N for v in ball})==N:witness.append(a)
out['351455']={'n':3,'t':2,'tile_size':N,'cyclic_homomorphisms_tested':tested,'tilings_found':witness,'scope':'Singleton-centered balls only; does not cover general component shapes.'}
# Hamming sphere divisibility diagnostics, not code existence.
rows=[]
for q in [6,10,12,14,15,18,20,21,22,24,26,28,30]:
 for e in [1,2]:
  hits=[]
  for n in range(2*e+1,101):
   size=sum(__import__('math').comb(n,j)*(q-1)**j for j in range(e+1))
   if pow(q,n,size)==0:hits.append(n)
  rows.append({'q':q,'errors':e,'n_range':[2*e+1,100],'sphere_divisibility_candidates':hits})
out['362979']=rows
Path('outputs/small-search.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
