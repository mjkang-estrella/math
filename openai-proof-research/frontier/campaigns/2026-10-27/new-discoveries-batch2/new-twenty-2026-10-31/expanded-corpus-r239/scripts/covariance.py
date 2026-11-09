import pathlib,json,time,itertools,functools
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1];start=time.monotonic()
@functools.lru_cache(None)
def trees(b):
 if b==0:return ((),)
 return tuple((a,c) for i in range(b) for a in trees(i) for c in trees(b-1-i))
def graph(t):
 adj=[[]];parent=[-1];children=[[]]
 def add(sub,p):
  v=len(adj);adj.append([p]);adj[p].append(v);parent.append(p);children.append([]);children[p].append(v)
  for child in sub:add(child,v)
 add(t,0)
 return adj,children
def unrooted(adj):
 def rec(v,p):return '('+''.join(sorted(rec(u,v) for u in adj[v] if u!=p))+')'
 return min(rec(v,-1) for v in range(len(adj)))
def calc(t):
 adj,child=graph(t);N=len(adj);E=N-1;S=list(itertools.combinations(range(N),2));C=len(S);idx={s:i for i,s in enumerate(S)}
 essential=[v for v in range(N) if len(child[v])==2];b=len(essential)
 def subtree(v):return {v}.union(*(subtree(u) for u in child[v]))
 coords=[(v,child[v][1],subtree(child[v][0])) for v in essential]
 edges=[];B=[[0]*b for s in S];ec=[0]*b;L=[[0]*C for s in S]
 for s,(x,y) in enumerate(S):
  for x0,other in [(x,y),(y,x)]:
   for z in adj[x0]:
    if z==other:continue
    target=idx[tuple(sorted((z,other)))];L[s][s]+=1;L[s][target]-=1
    for j,(p,c,side) in enumerate(coords):
     if other in side:
      if (x0,z)==(p,c):B[s][j]+=1;ec[j]+=1
      elif (z,x0)==(p,c):B[s][j]-=1
 assert all(sum(row[j] for row in B)==0 for j in range(b))
 # grounded Laplacian: Fraction Gaussian elimination with b right sides.
 M=[[F(x) for x in L[i][:-1]+B[i]] for i in range(C-1)];d=C-1
 for k in range(d):
  pivot=M[k][k];assert pivot
  for i in range(k+1,d):
   if not M[i][k]:continue
   q=M[i][k]/pivot
   for j in range(k+1,d+b):M[i][j]-=q*M[k][j]
   M[i][k]=F(0)
 X=[[F(0)]*b for _ in S]
 for i in reversed(range(d)):
  for j in range(b):X[i][j]=(M[i][d+j]-sum(M[i][k]*X[k][j] for k in range(i+1,d)))/M[i][i]
 result=[[F(2,C*E)*((ec[i] if i==j else 0)-sum(F(B[s][i])*X[s][j] for s in range(C))) for j in range(b)] for i in range(b)]
 assert all(result[i][j]==result[j][i] for i in range(b) for j in range(b))
 return tuple(tuple(str(x) for x in row) for row in result),unrooted(adj),N
rows=[];collisions=[]
for b in range(1,6):
 seen={};count=0
 for t in trees(b):
  if time.monotonic()-start>105:break
  mat,abstract,N=calc(t);key=str(mat);count+=1
  if key in seen and seen[key]['abstract']!=abstract:collisions.append({'first':seen[key],'second':{'tree':t,'abstract':abstract},'matrix':mat})
  else:seen[key]={'tree':t,'abstract':abstract}
 rows.append({'branch_vertices':b,'vertices':2*b+2,'ordered_rooted_binary_shapes_total':len(trees(b)),'shapes_computed':count,'distinct_matrices':len(seen),'abstract_collision_count_so_far':len(collisions)});print(rows[-1],flush=True)
(D/'covariance-search.json').write_text(json.dumps({'rows':rows,'seconds':time.monotonic()-start,'collisions':collisions,'claim':'Exact rational diagnostics using Theorem 2.10 star-move indicators and grounded configuration Laplacian; semantic bridge not formalized. Abstract isomorphism used to discard planar/root convention failures.'},indent=2)+'\n')
