import sys,json,pathlib,hashlib
D=pathlib.Path(__file__).resolve().parents[1];N=int(sys.argv[1]);mod=1<<24;a=[0]*N;a[0]=1
# q f2 f3^2 f12^2/(f1^2 f6), equation 1.1, retain coefficients through q^N.
for j in range(1,N):
 e=-2+(j%2==0)+2*(j%3==0)-(j%6==0)+2*(j%12==0)
 for _ in range(abs(e)):
  if e<0:
   for k in range(j,N):a[k]=(a[k]+a[k-j])%mod
  else:
   for k in range(N-1,j-1,-1):a[k]=(a[k]-a[k-j])%mod
p=[0]+a;fails=[];checks=[0]*4
for k in range(14):
 for n in range(N//(3*(1<<k))+1):
  inds=[3*(1<<k)*n,3*(1<<(k+1))*n+3*(1<<k),3*(1<<(k+2))*n+3*(1<<k),3*(1<<(k+2))*n+9*(1<<k)]
  for t,i in enumerate(inds):
   if i>N:continue
   checks[t]+=1
   if p[i]%(1<<(k+2)):fails.append(dict(clause=t+1,k=k,n=n,index=i,residue=p[i]%(1<<(k+2))))
out=dict(N=N,modulus=mod,checks=checks,failures=fails,initial=p[:25],coefficient_sha256=hashlib.sha256(json.dumps(p).encode()).hexdigest())
(D/f'pdo-{N}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
