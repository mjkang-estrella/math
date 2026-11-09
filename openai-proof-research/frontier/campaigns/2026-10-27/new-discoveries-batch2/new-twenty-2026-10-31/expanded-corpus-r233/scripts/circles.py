import pathlib,json,random,functools,itertools
P=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(233)
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def arrangement(n,normals=None):
 normals=[] if normals is None else list(normals)
 while len(normals)<n:
  v=tuple(rng.randrange(-50,51) for _ in range(3))
  if v==(0,0,0) or any(cross(v,w)==(0,0,0) for w in normals):continue
  if any(dot(v,cross(a,b))==0 for a,b in itertools.combinations(normals,2)):continue
  normals.append(v)
 pts=[];rings=[[] for _ in normals]
 for i,j in itertools.combinations(range(n),2):
  v=cross(normals[i],normals[j]);idx=len(pts);pts.extend([v,tuple(-a for a in v)])
  rings[i].extend([idx,idx+1]);rings[j].extend([idx,idx+1])
 adj=[set() for _ in pts]
 for v,ring in zip(normals,rings):
  e=next(e for e in [(1,0,0),(0,1,0),(0,0,1)] if cross(v,e)!=(0,0,0));u=cross(v,e);w=cross(v,u)
  def compare(i,j):
   a,b=dot(u,pts[i]),dot(w,pts[i]);c,d=dot(u,pts[j]),dot(w,pts[j])
   h1=b<0 or (b==0 and a<0);h2=d<0 or (d==0 and c<0)
   if h1!=h2:return 1 if h1 else -1
   det=a*d-b*c;return -1 if det>0 else 1 if det<0 else 0
  ring.sort(key=functools.cmp_to_key(compare))
  for a,b in zip(ring,ring[1:]+ring[:1]):adj[a].add(b);adj[b].add(a)
 assert all(len(a)==4 for a in adj)
 return normals,adj
def color(adj):
 colors=[-1]*len(adj);nodes=0
 def go(left):
  nonlocal nodes
  nodes+=1
  if nodes>100000:raise TimeoutError
  if not left:return True
  v=max(left,key=lambda x:(len({colors[u] for u in adj[x] if colors[u]>=0}),sum(colors[u]<0 for u in adj[x])))
  banned={colors[u] for u in adj[v]};used=max(colors)+1
  for c in range(min(3,used+1)):
   if c in banned:continue
   colors[v]=c
   if go(left-{v}):return True
  colors[v]=-1;return False
 try:r=go(set(range(len(adj))))
 except TimeoutError:return 'node_limit',nodes,None
 if r:assert all(colors[u]!=colors[v] for u in range(len(adj)) for v in adj[u])
 return '3-colorable' if r else 'uncolorable',nodes,colors if r else None
if __name__=='__main__':
 rows=[]
 for n in [9,10,11,12,14,16,18,20]:
  for sample in range(3):
   normals,adj=arrangement(n);status,nodes,colors=color(adj)
   row={'n':n,'sample':sample,'normals':normals,'status':status,'nodes':nodes,'colors':colors};rows.append(row)
   print(json.dumps({k:v for k,v in row.items() if k not in ['normals','colors']}),flush=True)
 (P/'inputs/circle-search.json').write_text(json.dumps(rows,indent=2))
