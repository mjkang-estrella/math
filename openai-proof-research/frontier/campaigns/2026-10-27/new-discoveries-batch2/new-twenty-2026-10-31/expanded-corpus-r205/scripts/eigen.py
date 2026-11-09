import itertools,math,json,sys,pathlib,time
D=pathlib.Path(__file__).resolve().parents[1]
def parts(n,m=None):
 if not n:yield ();return
 for i in range(min(n,m or n),1-1,-1):
  for p in parts(n-i,i):yield (i,)+p
def fixed(ct,r):
 a=[1]+[0]*r
 for c in ct:
  for j in range(r,c-1,-1):a[j]+=a[j-c]
 return a[r]
def cyc(p):
 seen=0;out=[]
 for i in range(len(p)):
  if seen>>i&1:continue
  j=i;c=0
  while not seen>>j&1:seen|=1<<j;c+=1;j=p[j]
  out.append(c)
 return tuple(sorted(out))
def val(mu):
 z=math.prod(x**mu.count(x)*math.factorial(mu.count(x)) for x in set(mu))
 return math.factorial(sum(mu))*2**(sum(mu)-len(mu))//z
out=[]
for k in range(int(sys.argv[1]),int(sys.argv[2])+1):
 t=time.monotonic(); rows={l:{} for l in range(1,k//2+1)}
 for mu in parts(k):
  # target matching alternates standard matching around cycles
  g=[];base=0
  for m in mu:
   for j in range(m):g.extend([2*(base+j)+1,2*(base+(j+1)%m)])
   base+=m
  hist={}
  for perm in itertools.permutations(range(k)):
   for flip in range(1<<k):
    p=[g[2*perm[i//2]+((i%2)^((flip>>(i//2))&1))] for i in range(2*k)]
    ct=cyc(p);hist[ct]=hist.get(ct,0)+1
  for l in rows:
   s=sum(c*(fixed(ct,2*l)-fixed(ct,2*l-1)) for ct,c in hist.items())*val(mu)
   assert s%(2**k*math.factorial(k))==0
   rows[l][mu]=s//(2**k*math.factorial(k))
 checks=[]
 for l,row in rows.items():
  target=(k-l,l);v=row[target];badmax=[(mu,x) for mu,x in row.items() if x>v]
  badsign=[(mu,x) for mu,x in row.items() if mu!=target and all(sum(mu[:j])>=sum(target[:j]) for j in range(1,len(mu)+len(target)+1)) and x>=0]
  checks.append({'l':l,'target':target,'value':v,'row':[(mu,x) for mu,x in row.items()],'larger_values':badmax,'nonnegative_above':badsign})
 out.append({'k':k,'checks':checks,'seconds':time.monotonic()-t});print(json.dumps(out[-1]),flush=True)
(D/'outputs'/f'eigen-{sys.argv[1]}-{sys.argv[2]}.json').write_text(json.dumps(out,indent=2))
