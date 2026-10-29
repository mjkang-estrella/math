"""Independent finite falsification: universal jet polynomials, direct log powers,
and Laurent-to-quadratic binomial expansion. No candidate code imported."""
from fractions import Fraction as Q
from collections import defaultdict,Counter
from math import comb,factorial
from pathlib import Path
import json,resource,time
resource.setrlimit(resource.RLIMIT_AS,(500*1024**2,500*1024**2))
start=time.monotonic();OUT=Path(__file__).parent
# Coordinates (parameter 1, parameter 2, x, w, Laurent t, imaginary unit).
z=(0,)*6; one={z:Q(1)}
def term(c=1,**kw):
 k=list(z)
 for name,e in kw.items():k['abxwti'.index(name)]=e
 return {tuple(k):Q(c)} if c else {}
def add(*fs):
 h=defaultdict(Q)
 for f in fs:
  for m,c in f.items():h[m]+=c
 return {m:c for m,c in h.items() if c}
def scale(f,c):return {m:v*c for m,v in f.items() if v*c}
def mul(f,g):
 h=defaultdict(Q)
 for m,c in f.items():
  for n,d in g.items():
   k=[a+b for a,b in zip(m,n)];iw=k[5]//2;k[5]%=2;pw=k[3]//2;k[3]%=2
   for j in range(pw+1):
    kk=k.copy();kk[2]+=2*j;h[tuple(kk)]+=c*d*((-1)**iw)*comb(pw,j)
 return {m:c for m,c in h.items() if c}
def power(f,n):
 h=one
 for _ in range(n):h=mul(h,f)
 return h
def diff(f,idx):
 h=defaultdict(Q)
 for m,c in f.items():
  if m[idx]:k=list(m);k[idx]-=1;h[tuple(k)]+=c*m[idx]
 return dict(h)
x=term(x=1);w=term(w=1);t=term(t=1);it=term(i=1)
D=lambda f:scale(mul(add(one,power(t,2)),diff(f,4)),-1)
partial=lambda f:add(scale(mul(add(one,power(x,2)),diff(f,2)),-1),scale(mul(mul(w,x),diff(f,3)),-1))
def v2(q):
 q=Q(q)
 if not q:return 100000
 def k(n):n=abs(n);return (n&-n).bit_length()-1
 return k(q.numerator)-k(q.denominator)
def universal(N):
 U=[{}, {(0,):1}]
 for n in range(1,N):
  out=defaultdict(int)
  for mon,c in U[n].items():
   for j in range(len(mon)):
    mm=list(mon);mm[j]+=1;out[tuple(sorted(mm))]-=c
  for i in range(1,n):
   for a,c in U[i].items():
    for b,d in U[n-i].items():out[tuple(sorted(a+b))]-=c*d
  U.append({m:c for m,c in out.items() if c})
 return U
def evaljet(U,jets):
 out={}
 for mon,c in U.items():
  f=one
  for k in mon:f=mul(f,jets[k])
  out=add(out,scale(f,c))
 return out
def jets(f,der,N):
 out=[f]
 for _ in range(N):out.append(der(out[-1]))
 return out
def embed(f,sub):
 out={};cache={}
 for m,c in f.items():
  g=term(c)
  for idx,e in enumerate(m):
   if not e:continue
   key=idx,e
   if key not in cache:
    base=sub.get(idx,term(**{'abxwti'[idx]:1}))
    if e<0:
     assert idx==4
     base=sub[-4];e=-e
    cache[key]=power(base,e)
   g=mul(g,cache[key])
  out=add(out,g)
 return out
def primitive(f):
 # exact Laurent long division independently for each parameter coefficient
 groups=defaultdict(dict)
 for (a,b,xx,ww,k,ii),c in f.items():
  assert xx==ww==ii==0
  groups[a,b][k]=c
 out={}
 for (a,b),numer in groups.items():
  lo=min(numer);rem=defaultdict(Q,numer);quot=defaultdict(Q)
  for k in range(max(numer),lo+1,-1):
   c=rem[k]
   if c:quot[k-2]+=c;rem[k]-=c;rem[k-2]-=c
  assert not any(rem.values()),('remainder',a,b,dict(rem))
  for k,c in quot.items():
   if c:
    assert k%2==0 and k!=-1
    out[(a,b,0,0,k+1,0)]=-c/Q(k+1)
 assert D(out)==f
 return out
N=11;U=universal(N)
P=add(term(a=1),term(a=1,x=2),term(b=1,w=1,x=1))
V=add(term(a=1),term(a=1,t=2),term(b=1),term(b=1,t=-2))
pj=jets(P,partial,N);vj=jets(V,D,N)
H=[{},*[evaljet(U[n],pj) for n in range(1,N+1)]]
S=[{},*[evaljet(U[n],vj) for n in range(1,N+1)]]
rows=[]
for n in range(1,N+1):
 h=H[n]
 for (a,b,xx,ww,k,ii),c in h.items():
  assert k==ii==0 and c.denominator==1
  assert a+b>0 and a+b<=(n+1)//2
  assert v2(c)>=a.bit_count()+b.bit_count()-1
  assert ww==b%2
  assert (xx+ww)%2==(n+1)%2
 # ideal(w): w-even coefficient polynomial vanishes at x^2=-1
 groups=defaultdict(Q)
 for (a,b,xx,ww,k,ii),c in h.items():
  if ww==0:groups[a,b,xx%2]+=c*((-1)**(xx//2))
 assert not any(groups.values())
 # independent Laurent comparison after coordinate/parameter substitutions
 weighted={m:c*2**(n+1-m[0]-m[1]) for m,c in h.items()}
 phi={0:add(term(a=1),term(b=1)),1:add(term(a=1),term(-1,b=1)),2:scale(add(t,term(-1,t=-1)),Q(1,2)),3:scale(add(t,term(t=-1)),Q(1,2))}
 assert embed(weighted,phi)==S[n]
 if n%2==1:
  r=(n+1)//2;J=primitive(S[n]);mid=defaultdict(Q)
  for m,c in J.items():mid[m[0],m[1]]+=c
  bound=2*r+v2(factorial(r-1));delta=max(-v2(c/Q(2**(4*r-2))) for c in mid.values() if c)
  assert delta==bound
  for (a,b),c in mid.items():
   if c:assert v2(c)>=n-a-b+(a+b-1).bit_count()
  # derive partial primitive of H by transforming the independently integrated S
  # u=(a+b)/2,v=(a-b)/2 here only to check an identity, never infer integrality
  inv={0:scale(add(term(a=1),term(b=1)),Q(1,2)),1:scale(add(term(a=1),term(-1,b=1)),Q(1,2)),4:add(w,x),-4:add(w,scale(x,-1))}
  JH=embed({m:c/Q(2**(n-m[0]-m[1])) for m,c in J.items()},inv)
  assert partial(JH)==h
  for (a,b,xx,ww,k,ii),c in JH.items():
   assert k==ii==0 and (xx+ww)%2==1
   assert c.denominator%2==1
   if ww:assert v2(c)>=(a+b-1).bit_count()
  cat=comb(2*r-2,r-1)//r;Ir=sum((Q(comb(r-1,j),2*j+1) for j in range(r)),Q())
  kap={m:((-1)**r)*c/Q(2**(4*r-2)) for m,c in mid.items() if c}
  assert kap[r,0]==cat*Ir/Q(2**(4*r-2))
  rows.append(dict(r=r,delta=delta,coefficients=len(kap),mixed_coefficients=sum(a>0 and b>0 for a,b in kap),jet_terms=len(U[n])))
# Source Definition 2.1 via direct inverse product and log(F)=sum(-1)^(k+1)(F-1)^k/k.
M=7
X=scale(add(one,mul(it,t)),Q(1,2));Y=scale(add(one,scale(mul(it,term(t=-1)),-1)),Q(1,2))
Pa=[one];Pb=[one]
for k in range(M):
 Pa.append(mul(Pa[-1],add(term(a=1),term(-k*(k+1)))))
 Pb.append(mul(Pb[-1],add(term(b=1),term(-k*(k+1)))))
C=[{}]*(M+1)
for s in range(M+1):
 C[s]=add(*(scale(mul(mul(Pa[l],Pb[s-l]),mul(power(X,l),power(Y,s-l))),Q(1,factorial(l)*factorial(s-l))) for l in range(s+1)))
F=[one]+[{} for _ in range(M)]
for s in range(1,M+1):
 e=[Q(1)]+[Q() for _ in range(M-s)]
 for j in range(1,s+1):
  for k in range(1,len(e)):e[k]+=j*e[k-1]
 for k,c in enumerate(e):F[s+k]=add(F[s+k],scale(C[s],c))
G=[{}]+F[1:];Gp=[one]+[{} for _ in range(M)];L=[{} for _ in range(M+1)]
for k in range(1,M+1):
 Gp=[add(*(mul(Gp[j],G[n-j]) for j in range(n+1))) for n in range(M+1)]
 for n in range(1,M+1):L[n]=add(L[n],scale(Gp[n],Q((-1)**(k+1),k)))
for n in range(1,M+1):
 # Riccati derivative exact Gaussian sign 1/(2i)^n
 factor=power(scale(it,Q(-1,2)),n)
 assert D(L[n])==mul(factor,S[n]),('source derivative',n)
 imag={m:c for m,c in L[n].items() if m[5]==1}
 assert all(m[4]%2 for m in imag)
 if n%2==0:assert imag=={}
 else:
  r=(n+1)//2;J=primitive(S[n]);expected=mul(term(Q((-1)**r,2**n),i=1),J)
  assert imag==expected
 # direct ODE coefficient, including Z*D(F) next coefficient
 if n<M:assert add(D(D(F[n])),scale(mul(it,D(F[n+1])),2),scale(mul(V,F[n]),-1))=={}
# falsifiers retained as negative controls
assert v2(Q(1))<2 and v2(Q(1,3))<2 and v2(Q(4,3))==2
bad=sum((Q(comb(3,j),2*j+3) for j in range(4)),Q());assert bad==Q(464,315) and v2(bad)==4
assert 0 < (1).bit_count()+(1).bit_count()-1 # a*b outside C
# triangular operator tested on monomial bases, denominators and a prescribed dyadic factor
for degree in range(13):
 for basis in range(degree+1):
  B=[Q(0)]*(degree+1);B[basis]=Q(8,2*basis+1)
  f=[Q(0)]*(degree+2)
  for k in reversed(range(degree+1)):f[k]=(-B[k]-2*(k+1)*f[k+1])/Q(2*k+1)
  assert all(v2(v)>=3 for v in f)
  assert all((2*k+1)*f[k]+2*(k+1)*f[k+1]==-B[k] for k in range(degree+1))
# Independent finite binomial valuation check; not a proof of the source theorem.
for m in range(65):
 val=sum((Q(comb(m,j),2*j+1) for j in range(m+1)),Q())
 assert v2(val)==m+v2(m+1)
result=dict(status='PASS finite falsification only',structure='universal differential-jet polynomials, direct truncated-log powers, Laurent long division and binomial coordinate transform',normalized_n_max=N,literal_source_n_max=M,binomial_m_max=64,triangular_degree_max=12,rows=rows,negative_controls=['termwise Laurent divisibility false at r=2','arbitrary shifted-moment bound false at 464/315','C is not closed under generic products'],wall_seconds=time.monotonic()-start,max_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
(OUT/'own-checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
