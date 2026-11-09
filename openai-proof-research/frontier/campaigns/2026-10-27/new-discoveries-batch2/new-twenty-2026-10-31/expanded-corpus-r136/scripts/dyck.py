import pathlib,json,collections
D=pathlib.Path(__file__).resolve().parents[1]
def partitions(n,m=None):
 if n==0:yield ();return
 for a in range(min(n,m or n),1-1,-1):
  for b in partitions(n-a,a):yield (a,)+b
def I(k,l):
 if l==0:return ()
 q,r=divmod(k,l);a=[l]*(1+q)+list(range(l-1,0,-1));b=[0]*(1+q)+[1]*r+[0]*(l-1-r);return tuple(x+y for x,y in zip(a,b))
def seed(lam):
 a=[]
 for i,v in enumerate(lam):
  b=I((v-1)*sum(lam[i+1:]),v-1)
  while len(a)<len(b):a.append(0)
  for j,x in enumerate(b):a[j]+=x
 return tuple(x for x in a if x)
def nu(a):
 if a and a[0]>len(a)+2:return None
 return tuple(x for x in (len(a)+1,)+tuple(x-1 for x in a) if x)
def rho(a):
 if nu(a) is None:return 0
 H=[i for i in range(len(a)-2) if a[i]==a[i+1]==a[i+2]]
 return a[H[-1]] if H else (a[0] if a else 0)
def inv(a):
 return sum(a[i]-j-sum(a[t]>j for t in range(i+1,len(a)))-1 in [0,1] for i in range(len(a)) for j in range(a[i]))
# arm=a_i-j-1; leg=number lower rows longer than j.
out=[];anomalies=[]
for k in range(1,25):
 count=checks=0;maxseed=maxdef=0
 for lam in partitions(k):
  a=seed(lam);f=sum((v-1)*sum(lam[i+1:]) for i,v in enumerate(lam));maxseed=max(maxseed,sum(a));maxdef=max(maxdef,f);count+=1
  if sum(a)-inv(a)!=f:anomalies.append(['seed deficit',lam,a,f])
  r=rho(a)
  for t in range(r+1):
   if a is None:anomalies.append(['undefined',lam,t]);break
   if sum(a)-inv(a)!=f:anomalies.append(['iterate deficit',lam,t]);break
   checks+=1;a=nu(a)
 rec={'lambda_size':k,'partitions':count,'R_iterates_checked':checks,'maximum_seed_size':maxseed,'maximum_deficit':maxdef};out.append(rec);print(json.dumps(rec),flush=True)
(D/'outputs/dyck.json').write_text(json.dumps({'coverage':out,'anomalies':anomalies,'limitation':'necessary seed and forced-R invariants only; NOT five-condition infinite-chain existence or n-oppositeness'},indent=2)+'\n')
print('ANOMALIES',anomalies[:10],flush=True)
