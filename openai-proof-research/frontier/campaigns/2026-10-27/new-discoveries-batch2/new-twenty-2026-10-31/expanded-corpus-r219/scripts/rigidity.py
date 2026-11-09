import itertools,random,json,sys
rng=random.Random(219);P=65521
n=int(sys.argv[1]);attempts=int(sys.argv[2]);cnt=dict(samples=0,mindegree=0,connected6=0,fullrank=0,deficient=0)
def conn(A,S):
 r=S&-S
 while True:
  t=r
  for i in range(n):
   if r>>i&1:t|=A[i]&S
  if t==r:return r==S
  r=t
def rank(M):
 b={}
 for a in M:
  for i in range(3*n):
   if a[i]:
    if i in b:
     c=a[i];a=[(x-c*y)%P for x,y in zip(a,b[i])]
    else:
     c=pow(a[i],-1,P);b[i]=[(x*c)%P for x in a];break
 return len(b)
for it in range(attempts):
 A=[0]*n
 for _ in range(rng.randrange(n,2*n)):
  for i,j in itertools.combinations(rng.sample(range(n),4),2):A[i]|=1<<j;A[j]|=1<<i
 cnt['samples']+=1
 if min(a.bit_count() for a in A)<6:continue
 cnt['mindegree']+=1;full=(1<<n)-1
 if any(not conn(A,full^sum(1<<v for v in C)) for C in itertools.combinations(range(n),5)):continue
 cnt['connected6']+=1
 pos=[[rng.randrange(P) for _ in range(3)] for _ in A];M=[]
 for i,j in itertools.combinations(range(n),2):
  if A[i]>>j&1:
   row=[0]*(3*n)
   for k in range(3):row[3*i+k]=(pos[i][k]-pos[j][k])%P;row[3*j+k]=-row[3*i+k]%P
   M.append(row)
 R=rank(M)
 if R==3*n-6:cnt['fullrank']+=1
 else:cnt['deficient']+=1;print('DEFICIENT',A,R,flush=True)
print(json.dumps(dict(n=n,seed=219,prime=P,counts=cnt)),flush=True)
