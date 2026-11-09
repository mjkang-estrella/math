import sys,pathlib,time,json,math
D=pathlib.Path(__file__).resolve().parents[1];mode=sys.argv[1];t0=time.monotonic()
if mode=='cycles':
 from array import array
 from sympy import bernoulli
 for n in range(1,12):
  b=2*n-1;N=1<<b;dp=array('Q',[0])*(N*b);allowed=[]
  for j in range(b):
   dp[(1<<j)*b+j]=1;allowed.append(sum(1<<k for k in range(b) if j<k or ((j+2)%2==0 and (k+2)%2==1)))
  for s in range(1,N):
   js=s
   while js:
    bit=js&-js;js-=bit;j=bit.bit_length()-1;v=dp[s*b+j]
    if not v:continue
    ks=allowed[j]&~s
    while ks:
     bit=ks&-ks;ks-=bit;k=bit.bit_length()-1;dp[(s|bit)*b+k]+=v
  ans=sum(dp[(N-1)*b+j] for j in range(b) if j%2==0)
  expected=abs(int(2*(1-2**(2*n))*bernoulli(2*n)))
  print('n',n,'cycles',ans,'Genocchi',expected,'equal',ans==expected,flush=True)
  assert ans==expected
elif mode=='fibonacci':
 import numpy as np
 N=100000000;label=np.zeros(N+1,dtype=np.int8);f=[0,1,1]
 while f[-1]+f[-2]<=N:f.append(f[-1]+f[-2])
 for t in range(2,len(f)-1):
  if f[t]+f[t-1]>N:break
  for b in range(1,min(f[t],(N-f[t])//f[t-1])+1):
   amax=min(b,(N-b*f[t-1])//f[t]);inds=b*f[t-1]+np.arange(1,amax+1)*f[t];label[inds]=1 if t%2==0 else 2
 assert np.all(label[2:]!=0)
 ds=np.flatnonzero(label==1);us=np.flatnonzero(label==2);out=[]
 for ell in [1,2,3,4,5,10,20,50,100,200,500]:
  dd=set(map(int,np.unique(ds[ell:]-ds[:-ell])));uu=set(map(int,np.unique(us[ell:]-us[:-ell])))
  out.append({'ell':ell,'D_only':sorted(dd-uu),'U_only':sorted(uu-dd),'D_size':len(dd),'U_size':len(uu)})
 (D/'outputs/fibonacci-gaps-large.json').write_text(json.dumps({'N':N,'D_count':len(ds),'U_count':len(us),'gaps':out},indent=2)+'\n')
 print('N',N,'D',len(ds),'U',len(us),'equal finite-prefix gap sets',sum(not x['D_only'] and not x['U_only'] for x in out),'of11; differences are not refutations')
elif mode=='valuations':
 N=20000;out=[]
 for k in [6,10,12,14,15,18,20,21,22,24,26,28,30]:
  for m in range(1,5):
   A=[0]*(N+1);A[0]=1;c=[(-1)**(i+1)*math.comb(k*m,i) for i in range(1,k*m+1)];d=[(-1)**i*math.comb(m,i) for i in range(m+1)];mx=0;arg=0
   for n in range(1,N+1):
    A[n]=sum(ci*A[n-i] for i,ci in enumerate(c,1) if i<=n)
    if n%k==0:A[n]+=sum(di*A[n//k-i] for i,di in enumerate(d) if i<=n//k)
    if A[n]<=0:raise RuntimeError('bad coefficient')
    z=A[n];v=0
    while z%k==0:v+=1;z//=k
    if v>mx:mx=v;arg=n
   r={'k':k,'m':m,'N':N,'maximum':mx,'first_argmax':arg};out.append(r);print(r,flush=True)
 (D/'outputs/valuations.json').write_text(json.dumps(out,indent=2)+'\n')
print('wall',time.monotonic()-t0)
