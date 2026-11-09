import pathlib,itertools,json,sys
D=pathlib.Path(__file__).resolve().parents[1]
def canon(g):
 def code(v,p):return '('+''.join(sorted(code(w,v) for w in g[v] if w!=p))+')'
 return min(code(v,-1) for v in range(len(g)))
def grow(g):
 n=len(g)
 for u in range(n):
  if len(g[u])<=1:yield g+[[u],[u,n+2],[n+1]],[(u,n),(u,n+1)]
  if len(g[u])==2:
   yield g+[[u,n+1],[n,n+2],[n+1]],[(u,n)]
   for v in g[u]:
    if len(g[v])==1:yield g+[[u,n+2],[v],[n]],[(u,n),(v,n+1)]
def dom(g,S):
 n=len(g);unit=1<<n
 for u in range(n):
  if S>>u&1:continue
  stack=[(u,-1,0)];weight=0
  while stack:
   v,p,d=stack.pop()
   if S>>v&1:weight+=1<<(n+1-d)
   else:stack.extend((w,v,d+1) for w in g[v] if w!=p)
  if weight<unit:return False
 return True
def smaller(g):
 n=len(g);k=(n+2)//3
 for z in range(1,k):
  for ss in itertools.combinations(range(n),z):
   S=sum(1<<v for v in ss)
   if dom(g,S):return list(ss)
 return None
pool={'()':[[]]}
for n in range(1,int(sys.argv[1])+1,3):
 if n==1:pool={'()':[[]]}
 else:
  new={}
  for g in pool.values():
   for h,edges in grow(g):
    h=[a[:] for a in h]
    for a,b in edges:h[a].append(b)
    new[canon(h)]=h
  pool=new
 hits=[]
 for i,g in enumerate(pool.values()):
  w=smaller(g)
  if w is not None:hits.append({'tree':g,'dominating_set':w})
 rec={'n':n,'construction_class_isomorphism_types':len(pool),'strictly_smaller_dominating_sets':hits,'scope':'all operation-generated trees at this order; exhaustive subsets smaller than (n+2)/3; reverse implication relies on source Lemma10 and is not re-proved'}
 print(json.dumps(rec),flush=True);(D/f'outputs/trees-{n}.json').write_text(json.dumps(rec,indent=2))
 if hits:break
