import json,pathlib,math,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for k in range(1,10):
 m=2**k;N=min(20000,128*m);c=[0]*(2*m);c[0]=1;prev=None;bad=[]
 for n in range(N+1):
  f=sum(c[:m])-sum(c[m:]);nu,r=divmod(n,2*m);s=(-1)**nu*f
  if r<=2*m-2:
   if s<=0:bad.append([n,'sign',f])
   if r and (s<prev or (s==prev and r!=2*m-2)):bad.append([n,'monotonicity',f])
  prev=s;c=[c[j]+c[j-1] for j in range(2*m)]
 z=dict(k=k,m=m,n_max=N,complete_intervals=(N+2)//(2*m),failures=bad);out.append(z);print(z,flush=True)
(D/'outputs/sparse.json').write_text(json.dumps(out,indent=2))
