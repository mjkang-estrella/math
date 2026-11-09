import pathlib,sys,json,math,itertools,collections
D=pathlib.Path(__file__).resolve().parents[1]
mode=sys.argv[1]
if mode=='permutation':
 N=int(sys.argv[2]);S=[[0]*(N+1) for _ in range(N+1)];I=[[0]*(N+1) for _ in range(N+1)];tot=[0]*(N+1); a=[0]*(N+1)
 for n in range(1,N+1):
  I[n][1]=int(n==1)
  for j in range(1,n):
   for k in range(1,n):I[n][k]+=a[j]*S[n-j][k]
  S[n]=I[n].copy()
  for j in range(1,n):
   for k in range(1,j+1):
    for l in range(1,n-j+1):S[n][k+l]+=I[j][k]*S[n-j][l]
  tot[n]=sum(S[n]);a[n]=sum(I[n]);ok=n<3 or (S[n][2]>=S[n][1] and all(S[n][k]>=S[n][k+1] for k in range(2,n)))
  print(json.dumps({'n':n,'distribution':S[n][:n+1],'ok':ok}),flush=True)
 if N>=7:
  for n in range(1,8):
   c=collections.Counter()
   for p in itertools.permutations(range(n)):
    if any(tuple(sorted(range(4),key=lambda i:p[t[i]])) in [(2,0,3,1),(1,3,0,2)] for t in itertools.combinations(range(n),4)):continue
    c[sum(all(p[i]>p[j] for j in range(i)) for i in range(n))]+=1
   assert [c[k] for k in range(n+1)]==S[n][:n+1],(n,c,S[n])
  print('independent permutation avoidance validation n<=7 PASS')
elif mode=='dyck':
 # Independently transcribed Appendix B, using integer comparisons throughout.
 def check(p,n):
  l=p-1; closest=next((q,((q+1)*n)//p) for q in range(l) if ((q+1)*n)%p==1); X=[(0,())]
  for z in range(l):
   Y=[]
   for d,x in X:
    for j in range(((z+1)*n)//p-sum(x)+1):
     xx=x+(j,);dd=d
     for k in range(1,len(xx)):
      b=p*sum(xx[k:])-n*(len(xx)-k)
      assert b
      dd+=min(xx[k-1],(-b)//p) if b<0 else min(xx[k],b//p)
     Y.append((dd,xx))
   X=Y
  M=sum(i*n//p for i in range(1,p)); lhs=collections.Counter();rhs=collections.Counter()
  for d,x in X:
   area=M-sum(sum(x[:i+1]) for i in range(l));dinv=M-d-area;lhs[area,M-d]+=1
   if sum(x[:closest[0]+1])==closest[1]:
    if area<=dinv:
     for j in range(area,dinv+1):rhs[j,M-d]+=1
    else:
     for j in range(dinv+1,area):rhs[j,M-d]-=1
  rhs=+rhs if all(v>=0 for v in rhs.values()) else rhs
  return len(X),lhs==rhs
 for p in range(2,10):
  for n in range(2,25):
   if math.gcd(p,n)!=1 or math.comb(p+n,p)//(p+n)>180000:continue
   c,ok=check(p,n);print(json.dumps({'p':p,'n':n,'paths':c,'ok':ok}),flush=True)
   if not ok:break
