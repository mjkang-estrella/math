import pathlib,json,math,time
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1];start=time.monotonic()
def add(a,b):
 c=[F(0)]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=x
 return c
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def interp(vals):
 p=[F(0)];basis=[F(1)];v=list(map(F,vals))
 for i in range(len(vals)):
  p=add(p,[x*v[0] for x in basis]);v=[b-a for a,b in zip(v,v[1:])]
  basis=[x/F(i+1) for x in mul(basis,[-i,1])]
 return p
def div(p,q):
 p=p[:];r=[F(0)]*(len(p)-len(q)+1)
 for i in reversed(range(len(r))):
  x=p[i+len(q)-1]/q[-1];r[i]=x
  for t,y in enumerate(q):p[i+t]-=x*y
 assert not any(p)
 return r
out=[]
for j in range(1,9):
 for k in range(0,13):
  m=2*k+1;degree=j+m;vals=[]
  for n in range(degree+2):
   dist=[1];sm=[0]
   for ell in range(1,j+1):
    nxt=[0]*(len(dist)+max(0,n))
    for a,c in enumerate(dist):
     for r in range(1,n+1):nxt[a+r]+=c
    dist=nxt;sm.append(sum(c*a**m for a,c in enumerate(dist)))
   vals.append(sum(math.comb(j*(n+1),q)*sm[j-q] for q in range(j)))
  p=interp(vals[:-1]);assert sum(x*F(degree+1)**i for i,x in enumerate(p))==vals[-1]
  q=[F(1)]
  for r in range(1,j):q=mul(q,[r,j])
  quotient=div(p,q)
  # Decompose in powers of n(n+1), requiring exact zero residual.
  rem=quotient[:];coeff=[]
  while len(rem)>1 and rem[-1]==0:rem.pop()
  for a in reversed(range(k+2)):
   power=[F(1)]
   for _ in range(a):power=mul(power,[0,1,1])
   lead=rem[2*a] if 2*a<len(rem) else F(0)
   coeff.append(str(lead))
   for i,x in enumerate(power):
    if i<len(rem):rem[i]-=lead*x
  assert not any(rem)
  out.append({'j':j,'k':k,'degree_bound':degree,'quotient_in_t_descending':coeff})
  print(j,k,'verified',flush=True)
(D/'outputs/polynomial-checks.json').write_text(json.dumps({'checks':out,'wall':time.monotonic()-start,'scope':'Exact rational interpolation diagnostics plus extra evaluation. General degree bound supplied by ordinary proof; no Lean endpoint.'},indent=2)+'\n')
