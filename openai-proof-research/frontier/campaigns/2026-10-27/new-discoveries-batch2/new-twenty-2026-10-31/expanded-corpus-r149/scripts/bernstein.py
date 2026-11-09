import random,itertools as it,json,time
r=random.Random(149);s=time.monotonic();p=1000003
def rank(M):
 A=[v[:] for v in M];k=0
 for c in range(len(A[0]) if A else 0):
  j=next((j for j in range(k,len(A)) if A[j][c]%p),None)
  if j is None:continue
  A[k],A[j]=A[j],A[k];v=pow(A[k][c],-1,p);A[k]=[x*v%p for x in A[k]]
  for j in range(k+1,len(A)):
   a=A[j][c]%p
   if a:A[j]=[(x-a*y)%p for x,y in zip(A[j],A[k])]
  k+=1
  if k==len(A):break
 return k
def coloring(E):
 c=[[r.randrange(-20,21),r.randrange(-20,21)] for _ in range(12)]
 for x in c:x.append(-sum(x))
 pars=[list(range(12)) for _ in range(3)]
 def root(P,x):
  while P[x]!=x:x=P[x]
  return x
 for a,b in E:
  scores=[c[a][i]+c[6+b][i] for i in range(3)];v=max(scores)
  if scores.count(v)>1:return None
  i=scores.index(v);P=pars[i];x=root(P,a);y=root(P,6+b)
  if x==y:return None
  P[x]=y
 return c
for size in [18,21,24,27]:
 independent=found=0;unresolved=[]
 for trial in range(50):
  X=[[r.randrange(1,p) for _ in range(3)] for _ in range(6)];Y=[[r.randrange(1,p) for _ in range(3)] for _ in range(6)]
  E=list(it.product(range(6),repeat=2));r.shuffle(E);basis=[];rows=[]
  for a,b in E:
   row=[0]*36;row[a*3:a*3+3]=Y[b];row[18+b*3:18+b*3+3]=X[a]
   if rank(rows+[row])>len(rows):rows.append(row);basis.append((a,b))
   if len(rows)==size:break
  if len(rows)<size:continue
  independent+=1
  for j in range(2000):
   c=coloring(basis)
   if c is not None:found+=1;break
  else:unresolved.append(basis)
 print(json.dumps(dict(m=6,n=6,d=3,edges=size,independent_specializations=independent,integer_labelings_per_graph=2000,bernstein_found=found,unresolved_count=len(unresolved),unresolved_examples=unresolved[:2],seconds=time.monotonic()-s)),flush=True)
