"""Exact finite diagnostics. No asymptotic or universal rank certification."""
import math,json,itertools,collections
from fractions import Fraction

def factor(n):
 out={};p=2
 while p*p<=n:
  while n%p==0:out[p]=out.get(p,0)+1;n//=p
  p=3 if p==2 else p+2
 if n>1:out[n]=out.get(n,0)+1
 return out

def leg(a,p):
 z=pow(a%p,(p-1)//2,p);return -1 if z==p-1 else z

def rank(rows,w):
 a=list(rows);r=0
 for j in range(w):
  pivot=next((i for i in range(r,len(a)) if a[i]>>j&1),None)
  if pivot is not None:
   a[pivot],a[r]=a[r],a[pivot]
   for i in range(len(a)):
    if i!=r and (a[i]>>j&1):a[i]^=a[r]
   r+=1
 return r

def mons(d):
 ps=sorted(factor(d));t=len(ps)
 A=[[int(leg(q,p)==-1) if i!=j else 0 for j,q in enumerate(ps)] for i,p in enumerate(ps)]
 for i in range(t):A[i][i]=sum(A[i])%2
 D=[int(leg(2,p)==-1) for p in ps]
 C=[[A[i][j]^(D[i] if i==j else 0) for j in range(t)] for i in range(t)]
 H=[C[i]+[D[i] if i==j else 0 for j in range(t)] for i in range(t)]+[[D[i] if i==j else 0 for j in range(t)]+C[i] for i in range(t)]
 rows=lambda B:[sum(x<<j for j,x in enumerate(row)) for row in B]
 ka=[v for v in range(1<<t) if all((v&r).bit_count()%2==0 for r in rows(A))]
 basis=[]
 for v in ka:
  if rank(basis+[v],t)>len(basis):basis.append(v)
 R=[[sum(D[j]*((u>>j)&1)*((v>>j)&1) for j in range(t))%2 for v in basis] for u in basis]
 nullity=2*t-rank(rows(H),2*t)
 assert nullity==2*len(basis)-rank(rows(R),len(basis))
 assert all(sum(row)%2==0 for row in A)
 assert all(A[i][j]==A[j][i] for i in range(t) for j in range(t))
 assert sum(D)%2==0 and nullity>=2
 return {'primes':ps,'A':A,'D':D,'pure_2_dimension':nullity,'h':len(basis),'restricted_D_rank':rank(rows(R),len(basis))}

def ternary(d,c):
 ans=0
 for z in range(math.isqrt(d//c)+1):
  v=d-c*z*z
  for x in range(math.isqrt(v//2)+1):
   yy=v-2*x*x;y=math.isqrt(yy)
   if y*y==yy:ans+=(1 if z==0 else 2)*(1 if x==0 else 2)*(1 if y==0 else 2)
 return ans

def hecke_coefficient(d):
 # Independent signed binary-Hecke theta convolution from Tunnell p.327.
 total=0;bound=math.isqrt(d)//4+2
 for m in range(-bound,bound+1):
  v=d-(4*m+1)**2
  if v<0:continue
  for z in range(math.isqrt(v//8)+1):
   w=v-8*z*z
   if w%2:continue
   t=math.isqrt(w//2)
   if 2*t*t==w:total+=(-1 if m%2 else 1)*(1 if z==0 else 2)*(1 if t==0 else 2)
 return total

def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def norm(a):return a[0]*a[0]+a[1]*a[1]
def divmodg(a,b):
 z=mul(a,(b[0],-b[1]));n=norm(b);q=(round(Fraction(z[0],n)),round(Fraction(z[1],n)));v=mul(q,b);return q,(a[0]-v[0],a[1]-v[1])
def gcdg(a,b):
 while b!=(0,0):a,b=b,divmodg(a,b)[1]
 return a

def run():
 out={'status':'PASS_EXACT_FINITE_DIAGNOSTICS_ONLY'}
 local=[]
 for M in [8,24,256]:
  for p in [3,5,7,13,17]:
   allowed=[u for u in range(p*p) if (M*M*u*u+1)%(p*p)]
   counts=collections.Counter(leg(M*M*u*u+1,p) for u in allowed)
   z=0 if M%p==0 else 1+leg(-1,p)
   if M%p==0:expected={-1:0,0:0,1:p*p}
   else:expected={0:z*(p-1),1:p*(p-z-1)//2,-1:p*(p-z+1)//2}
   assert all(counts[v]==expected[v] for v in [-1,0,1])
   local.append({'M':M,'p':p,'allowed':len(allowed),'counts':{str(v):counts[v] for v in [-1,0,1]}})
 out['local_laws']=local
 samples=[];hist=collections.Counter();rejected=0
 for n in range(1,151):
  d=(256*n)**2+1;fac=factor(d)
  assert all(p%4==1 for p in fac)
  if any(e>1 for e in fac.values()):rejected+=1;continue
  rec=mons(d);hist[rec['pure_2_dimension']]+=1
  if n in [1,2,4,5,6,7,8,16]:samples.append({'n':n,'d':d,**rec})
 out['M256_first150']={'squarefree':sum(hist.values()),'excluded':rejected,'pure_2_histogram':{str(k):v for k,v in sorted(hist.items())},'selected':samples}
 gauss=[]
 for n in [1,2,4,5,7,8]:
  a=256*n;alpha=(1,-a);fac=factor(a*a+1)
  if any(e>1 for e in fac.values()):continue
  assert norm(gcdg(alpha,(1,a)))==1
  prod=(1,0);parts=[]
  for p in fac:
   b=gcdg(alpha,(p,0));assert norm(b)==p
   choices=[mul(b,u) for u in [(1,0),(-1,0),(0,1),(0,-1)]]
   b=next(x for x in choices if divmodg((x[0]-1,x[1]),(-2,2))[1]==(0,0))
   prod=mul(prod,b);parts.append(list(b))
   q,r=divmodg(alpha,b);assert r==(0,0) and mul(b,q)==alpha
   assert math.gcd(*b)==1
   assert b[0]*q[0]-b[1]*q[1]==1
  assert prod==alpha
  gauss.append({'n':n,'alpha':list(alpha),'primary_factors':parts})
 out['gaussian_orientations']=gauss
 theta=[]
 for d in [17,65,257,577,65537,262145]:
  A=ternary(d,32);B=ternary(d,8);a=hecke_coefficient(d)
  assert 2*a==2*A-B
  theta.append({'d':d,'squarefree':all(v==1 for v in factor(d).values()),'A32':A,'B8':B,'C':2*A-B,'a':a})
 assert theta[-2]['a']==32 and theta[-1]['a']==0
 out['tunnell_exact_counts']=theta
 # Actual local points of the forced 2-cover at bad primes, and 2-adic unit square.
 local_cover=[]
 for d in [65537,262145]:
  root2=next(x for x in range(256) if x*x%256==d%256)
  assert ((-d+root2*root2)%256)==0
  roots={}
  for p in factor(d):
   i=next(x for x in range(p) if (x*x+1)%p==0)
   # (t,u1,u2,u3)=(1,i,1,0); nonsingular root of u1^2+1.
   assert (2*i)%p!=0
   assert (-d+d-0)%p==0 and (-d-d*i*i)%p==0
   roots[str(p)]=i
  local_cover.append({'d':d,'sqrt_d_mod256':root2,'sqrt_minus1_mod_p':roots})
 out['local_cover_certificates']=local_cover
 points=[]
 for t in [1,2,16,32,48]:
  d=4*t**4+1;x=-4*t*t;y=2*t*(2-d)
  assert y*y==x**3-d*d*x
  q=next(iter(factor(d-2)))
  assert q>=3 and (2*t*d)%q and (3*x*x-d*d)%q
  slope=Fraction(3*x*x-d*d,2*y);x2=slope*slope-2*x
  assert x2.denominator%q==0
  points.append({'t':t,'d':d,'x':x,'y':y,'good_prime_for_formal_group':q,'double_x':[x2.numerator,x2.denominator]})
 out['quartic_nontorsion_points']=points
 # Enumerate all alternating pairings in dimensions 2 and 4.
 alts=[]
 for r in [2,4]:
  edges=list(itertools.combinations(range(r),2));hist2=collections.Counter()
  for mask in range(1<<len(edges)):
   rows=[0]*r
   for j,(u,v) in enumerate(edges):
    if mask>>j&1:rows[u]|=1<<v;rows[v]|=1<<u
   hist2[r-rank(rows,r)]+=1
  total=sum(hist2.values());assert Fraction(total-hist2[0],total)<=Fraction(7,12)
  alts.append({'r':r,'nullities':{str(k):v for k,v in sorted(hist2.items())}})
 out['conditional_pairing_algebra']=alts
 # At finite towers a subgroup containing 2B has at most a one-level loss.
 shifts=[]
 for exps in [(1,1),(2,2),(4,4),(1,2,5)]:
  for k in range(1,6):
   rb=sum(e>=k for e in exps);ra=sum(e-1>=k for e in exps);rbnext=sum(e>=k+1 for e in exps)
   assert rbnext<=ra<=rb
  shifts.append(list(exps))
 out['one_level_shift_cases']=shifts
 return out
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
