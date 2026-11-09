import itertools,math,json,time,sys
p=int(sys.argv[1]);m=int(sys.argv[2]);q=p**m;start=time.monotonic()
def coeff(x):
 a=[]
 for _ in range(m):a.append(x%p);x//=p
 return a
D=[coeff(x) for x in range(q)]
def rem(f,g):
 f=f[:]
 while f and not f[-1]:f.pop()
 while len(f)>=len(g):
  z=f[-1]*pow(g[-1],-1,p)%p;d=len(f)-len(g)
  for i,v in enumerate(g):f[d+i]=(f[d+i]-z*v)%p
  while f and not f[-1]:f.pop()
 return f
irr=None
for cs in itertools.product(range(p),repeat=m):
 if not cs[0]:continue
 f=list(cs)+[1]
 if all(rem(f,list(g)+[1]) for deg in range(1,m//2+1) for g in itertools.product(range(p),repeat=deg)):
  irr=f;break
assert irr

def add(a,b):return sum((x+y)%p*p**i for i,(x,y) in enumerate(zip(D[a],D[b])))
def mul(a,b):
 z=[0]*(2*m-1)
 for i,x in enumerate(D[a]):
  for j,y in enumerate(D[b]):z[i+j]=(z[i+j]+x*y)%p
 for d in range(2*m-2,m-1,-1):
  for i in range(m):z[d-m+i]=(z[d-m+i]-z[d]*irr[i])%p
 return sum(z[i]*p**i for i in range(m))
def power(a,n):
 z=1
 while n:
  if n&1:z=mul(z,a)
  a=mul(a,a);n//=2
 return z
for ell in range(1,m):
 if math.gcd(ell,m)!=1:continue
 B={add(power(x,p**ell+1),x) for x in range(q)};k=q-(p*q-1)//(2*(p+1))
 s=0
 for x in B:s=add(s,x)
 mean=mul(s,pow(len(B)%p,-1,p));neg=sum((-v)%p*p**i for i,v in enumerate(D[mean]));C={add(x,neg) for x in B}
 stab=[]
 for a in range(1,q):
  if all(mul(a,x) in C for x in C):stab.append(a)
 print(json.dumps({'p':p,'m':m,'ell':ell,'modulus':irr,'image_size':len(B),'expected_size':k,'affine_stabilizer_scalars':stab,'centroid':mean,'elapsed':time.monotonic()-start}),flush=True)
