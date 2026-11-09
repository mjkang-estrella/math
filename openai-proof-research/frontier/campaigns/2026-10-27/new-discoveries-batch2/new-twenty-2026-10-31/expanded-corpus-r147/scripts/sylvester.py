import itertools,random,time,json,pathlib,sys,math
D=pathlib.Path(__file__).resolve().parents[1]; n=int(sys.argv[1]);N=2**n;m=(2*N+(-1)**n)//3;bound=((3*n+7)*N+2*(-1)**n)//9
H=[[(-1)**((a&b).bit_count()%2) for b in range(N)] for a in range(N)]
best=10**20;bestS=[];steps=0;start=time.monotonic();rng=random.Random(147+n)
def evaluate(S):return [sum(H[a][b] for a in S) for b in range(N)]
if n<=4:
 for S in itertools.combinations(range(N),m):
  w=evaluate(S);v=sum(map(abs,w));steps+=1
  if v<best:best,bestS=v,list(S)
else:
 restart=0
 while time.monotonic()-start<80:
  allS=list(range(N))
  if restart:rng.shuffle(allS)
  w=evaluate(allS[:m]);v=sum(map(abs,w))
  if v<best:best,bestS=v,allS[:m]
  for t in range(10000):
   i=rng.randrange(m);j=rng.randrange(m,N);a,b=allS[i],allS[j];new=[z-x+y for z,x,y in zip(w,H[a],H[b])];v2=sum(map(abs,new));temp=max(.1,3*(1-t/10000)) if restart%3==0 else .01
   if v2<=v or rng.random()<math.exp(min(0,(v-v2)/temp)):
    w,v=new,v2;allS[i],allS[j]=b,a
    if v<best:best,bestS=v,allS[:m]
   steps+=1
   if steps%500==0 and time.monotonic()-start>=80:break
  restart+=1
  if best<bound:break
rec=dict(n=n,N=N,m=m,bound=bound,best=best,subset=bestS,steps=steps,exhaustive=n<=4,seconds=time.monotonic()-start)
(D/f'outputs/sylvester{n}.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec)
