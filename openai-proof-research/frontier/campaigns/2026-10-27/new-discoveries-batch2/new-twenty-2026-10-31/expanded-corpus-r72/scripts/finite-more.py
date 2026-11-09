import pathlib,sys,json,itertools,math,functools,collections
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'vendor'));mode=sys.argv[1];out={}
if mode=='poly':
 def F(L,x):return 1 if not L else x*math.prod(x+sum(L)-j for j in range(1,len(L)))
 count=0;bad=[]
 for d in range(5):
  for L in itertools.product([-1,0,1,2],repeat=d):
   for x,y in itertools.product(range(-2,3),repeat=2):
    lhs=sum(F([L[i] for i in range(d) if mask>>i&1],x)*F([L[i] for i in range(d) if not mask>>i&1],y) for mask in range(1<<d));count+=1
    if lhs!=F(L,x+y):bad.append((L,x,y,lhs))
 out=dict(lengths=list(range(5)),lambda_values=[-1,0,1,2],x_y_values=list(range(-2,3)),k=2,checks=count,failures=bad)
elif mode=='hom':
 import networkx as nx
 atlas=nx.graph_atlas_g();Hs=[H for H in atlas if 2<=len(H)<=4 and nx.is_connected(H)];out=[]
 def homs(G,H):return [f for f in itertools.product(range(len(H)),repeat=len(G)) if all(H.has_edge(f[a],f[b]) for a,b in G.edges())]
 for H in Hs:
  chi=next(k for k in range(2,len(H)+1) if homs(H,nx.complete_graph(k)));boards=0;witness=None
  for G in atlas:
   if not (1<=len(G)<=5) or max(dict(G.degree()).values())>=chi:continue
   boards+=1;F=homs(G,H)
   if not F:continue
   seen={F[0]};q=[F[0]];fs=set(F)
   for f in q:
    for v in range(len(G)):
     for c in range(len(H)):
      g=f[:v]+(c,)+f[v+1:]
      if g in fs and g not in seen:seen.add(g);q.append(g)
   if len(seen)<len(F):witness=dict(board_edges=list(G.edges()),order=len(G),hom_count=len(F),component_size=len(seen));break
  out.append(dict(H_edges=list(H.edges()),H_order=len(H),chromatic_number=chi,boards_checked=boards,witness=witness))
elif mode=='pseudo':
 import numpy as np,sympy as s
 from scipy.spatial import HalfspaceIntersection
 P=list(range(1,8));lines=[[p for p in P if (p&l).bit_count()%2==0] for l in P];A=[]
 for p in P:A.append([int(i==p) for i in P])
 for line in lines:
  for p in line:A.append([(-1 if i==p else 1) if i in line else 0 for i in P])
 A=np.array(A);hs=np.column_stack((-(A[:,:6]-A[:,6,None]),-A[:,6]));vertices=HalfspaceIntersection(hs,np.ones(6)/7).intersections;rays=set()
 for v in vertices:
  w=[s.Rational(float(x)).limit_denominator(100000) for x in [*v,1-sum(v)]];den=s.ilcm(*(x.q for x in w));z=tuple(int(x*den) for x in w);g=math.gcd(*z);z=tuple(x//g for x in z)
  assert all(sum(int(a)*b for a,b in zip(row,z))>=0 for row in A);active=[list(map(int,row)) for row in A if sum(int(a)*b for a,b in zip(row,z))==0];assert s.Matrix(active).rank()==6;rays.add(z)
 noncode=[z for z in rays if not (set(z)<={0,1} and all(sum(z[p-1] for p in l)%2==0 for l in lines))];weights=[s.Rational(sum(z)**2,sum(t*t for t in z)) for z in noncode];m=min(weights);winners=[z for z,w in zip(noncode,weights) if w==m];out=dict(q=2,points=7,inequalities=len(A),rays=len(rays),noncode_rays=len(noncode),minimum_noncode_AWGNC=str(m),minimizers=winners,all_minimizers_012=all(set(z)<={0,1,2} and 1 in z and 2 in z for z in winners),enumeration='Qhull vertices; each recovered ray checked exactly and active rank 6, completeness still numerical')
(D/f'outputs/{mode}.json').write_text(json.dumps(out,indent=2));print(out)
