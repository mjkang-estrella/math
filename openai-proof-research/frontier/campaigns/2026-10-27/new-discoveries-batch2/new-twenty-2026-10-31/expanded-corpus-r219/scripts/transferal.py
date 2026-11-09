import itertools,random,json,sys
n=int(sys.argv[1]);mode=sys.argv[2];P=65521;rng=random.Random(219+n)
edges=list(itertools.combinations(range(n),2));ei={e:i for i,e in enumerate(edges)};tris=[tuple(ei[e] for e in itertools.combinations(t,2)) for t in itertools.combinations(range(n),3)];E=len(edges)
def rank(rows):
 basis={}
 for row in rows:
  a=row[:]
  for i in range(E):
   if a[i]:
    if i in basis:
     b=basis[i];v=a[i];a=[(x-v*y)%P for x,y in zip(a,b)]
    else:
     v=pow(a[i],-1,P);basis[i]=[(x*v)%P for x in a];break
 return len(basis)
def matching(sel):
 owners={}
 def aug(t,seen):
  for e in tris[t]:
   if e in seen:continue
   seen.add(e)
   if e not in owners or aug(owners[e],seen):owners[e]=t;return True
  return False
 return all(aug(t,set()) for t in sel)
def matrix():
 x=[rng.randrange(1,P) for _ in edges];M=[]
 for t in tris:
  row=[0]*E;s=sum(x[e] for e in t)
  for e in t:row[e]=(s-2*x[e])%P
  M.append(row)
 return M
M=matrix();count=match=fail=0;bad=[]
if mode=='exhaustive':selections=itertools.combinations(range(len(tris)),min(E,len(tris)))
else:selections=(tuple(sorted(rng.sample(range(len(tris)),rng.randrange(max(1,E-6),min(E,len(tris))+1)))) for _ in range(int(sys.argv[3])))
for sel in selections:
 count+=1
 if not matching(sel):continue
 match+=1
 if rank([M[t] for t in sel])<len(sel):
  N=matrix()
  if rank([N[t] for t in sel])<len(sel):fail+=1;bad.append(sel);print('PERSISTENT DEFICIENCY',sel,flush=True)
 if count%2000==0:print('progress',n,count,match,fail,flush=True)
print(json.dumps(dict(n=n,mode=mode,total=count,matching=match,persistent_rank_deficiency=fail,bad=bad,prime=P,seed=219+n)),flush=True)
