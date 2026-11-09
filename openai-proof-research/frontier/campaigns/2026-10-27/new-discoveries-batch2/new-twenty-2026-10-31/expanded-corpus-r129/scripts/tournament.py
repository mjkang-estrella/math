import json,sys
N=int(sys.argv[1]);best=[0]*(N+1);arg=[None]*(N+1);patterns=[0]*(N+1)
def dfs(a,mask,n):
 count=sum(a);sym=all(((mask>>i)&1)!=((mask>>(n-2-i))&1) for i in range(n-1));count//=2 if sym and n>1 else 1
 patterns[n]+=1
 if count>best[n]:best[n]=count;arg[n]=mask
 if n==N:return
 b=[0];s=0
 for v in a:s+=v;b.append(s)
 dfs(b,mask|(1<<(n-1)),n+1)
 dfs([s-v for v in b],mask,n+1)
def direct(n,mask):
 a=[1]
 for k in range(n-1):
  s=0;b=[0]
  for v in a:s+=v;b.append(s)
  a=b if (mask>>k)&1 else [s-v for v in b]
 count=sum(a);sym=all(((mask>>i)&1)!=((mask>>(n-2-i))&1) for i in range(n-1));return count//(2 if sym else 1)
dfs([1],0,1)
for n in range(5,N+1):
 target=sum(1<<j for j in range(n-1) if (j%2==0 if n%2==0 else j==0 or j>=3 and j%2==1))
 print(json.dumps({'n':n,'patterns':patterns[n],'maximum':best[n],'arg':arg[n],'hypothesized':direct(n,target),'ok':best[n]<=direct(n,target)}),flush=True)
