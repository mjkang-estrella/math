import itertools,random,json,sys
rng=random.Random(219);P=65521
base=int(sys.argv[1]);reps=int(sys.argv[2]);counts=dict(generated=0,connected6=0,rank_full=0,rank_deficient=0)
def kconn(A,k):
 n=len(A)
 for s,t in itertools.combinations(range(n),2):
  if t in A[s]:continue
  cap=[[0]*(2*n) for _ in range(2*n)]
  for v in range(n):
   cap[2*v][2*v+1]=k if v in (s,t) else 1
   for w in A[v]:cap[2*v+1][2*w]=k
  total=0
  while total<k:
   prev=[-1]*(2*n);prev[2*s+1]=2*s+1;q=[2*s+1]
   for v in q:
    for w in range(2*n):
     if cap[v][w] and prev[w]<0:prev[w]=v;q.append(w)
    if prev[2*t]>=0:break
   if prev[2*t]<0:return False
   w=2*t
   while w!=2*s+1:v=prev[w];cap[v][w]-=1;cap[w][v]+=1;w=v
   total+=1
 return True
def rank(M):
 b={}
 for a in M:
  for i in range(len(a)):
   if a[i]:
    if i in b:
     c=a[i];a=[(x-c*y)%P for x,y in zip(a,b[i])]
    else:
     c=pow(a[i],-1,P);b[i]=[(x*c)%P for x in a];break
 return len(b)
for it in range(reps):
 E={tuple(sorted((i,(i+d)%base))) for i in range(base) for d in (1,2)}
 for _ in range(20*base):
  (a,b),(c,d)=rng.sample(sorted(E),2)
  if len({a,b,c,d})<4:continue
  if rng.randrange(2):c,d=d,c
  f,g=tuple(sorted((a,c))),tuple(sorted((b,d)))
  if f in E or g in E:continue
  E.remove(tuple(sorted((a,b))));E.remove(tuple(sorted((c,d))));E.update([f,g])
 edges=sorted(E);n=len(edges);A=[set() for _ in edges]
 for i,j in itertools.combinations(range(n),2):
  if set(edges[i])&set(edges[j]):A[i].add(j);A[j].add(i)
 counts['generated']+=1
 if not kconn(A,6):continue
 counts['connected6']+=1
 pos=[[rng.randrange(P) for _ in range(3)] for _ in A];M=[]
 for i,j in itertools.combinations(range(n),2):
  if j in A[i]:
   row=[0]*(3*n)
   for k in range(3):row[3*i+k]=(pos[i][k]-pos[j][k])%P;row[3*j+k]=-row[3*i+k]%P
   M.append(row)
 R=rank(M);counts['rank_full' if R==3*n-6 else 'rank_deficient']+=1
 if R<3*n-6:print('DEFICIENT',edges,R,flush=True)
print(json.dumps(dict(base_order=base,line_graph_order=2*base,seed=219,prime=P,counts=counts)),flush=True)
