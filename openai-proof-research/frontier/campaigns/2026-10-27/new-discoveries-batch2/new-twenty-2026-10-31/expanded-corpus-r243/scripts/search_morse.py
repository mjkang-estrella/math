import json,time
N=3000;mod=5**15;dp=[1];bad=[];start=time.monotonic();maxv=0
for t in range(1,2*N+1):
 new=[0]*(t+1)
 for h,v in enumerate(dp):
  new[h+1]=(new[h+1]+v*(2*h+1)**2)%mod
  if h:new[h-1]=(new[h-1]+v)%mod
 dp=new
 if t%2==0 and t>=8:
  n=t//2;x=dp[0];v=0
  while x and x%5==0:x//=5;v+=1
  want=2
  if n%2:
   z=4*n-15;want=3
   while z%5==0:z//=5;want+=1
  if v!=want:bad.append([n,v,want])
  maxv=max(maxv,v)
 if t%1000==0:print(json.dumps({'n':t//2,'failures':bad[:5],'max_valuation':maxv,'elapsed':time.monotonic()-start}),flush=True)
