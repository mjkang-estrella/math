import pathlib,json,numpy as np
D=pathlib.Path(__file__).resolve().parents[1];N=1200
p=[0]*(N+1);p[0]=1
for n in range(1,N+1):
 for j in range(1,n+1):
  a=j*(3*j-1)//2;b=j*(3*j+1)//2
  if a>n:break
  sign=1 if j%2 else -1;p[n]+=sign*p[n-a]
  if b<=n:p[n]+=sign*p[n-b]
p=np.array(p,dtype=object);out=[]
for k in range(2,31):
 bad=[];tests=0;threshold=k+1+36*(k==2)+6*(k==3)
 for m in range(N-k):
  diff=np.zeros(N+1,dtype=object)
  for j in range(1,N):
   e=j*((2*k-1)*j-1)//2+m*j
   if e>N:break
   sign=1 if j%2 else -1
   diff[e:]+=sign*p[:N+1-e]
   if e+j<=N:diff[e+j:]-=2*sign*p[:N+1-e-j]
   if e+2*j<=N:diff[e+2*j:]+=sign*p[:N+1-e-2*j]
  start=max(threshold,m+k+1)
  for n in range(start,N+1):
   tests+=1
   if diff[n]<0:bad.append([m,n,int(diff[n])])
 out.append(dict(k=k,n_min=threshold,n_max=N,adjacent_comparisons=tests,failures=bad));print(k,tests,len(bad),flush=True)
 (D/'outputs/garvan.json').write_text(json.dumps(out,indent=2))
