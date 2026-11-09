import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];N=40;C=20
# Coefficients through q^40. Tail bounds documented in mathematical-attempts.md.
def mul(a,b):
 c=[0]*(N+1)
 for i,x in enumerate(a):
  if x:
   for j in range(N+1-i):c[i+j]+=x*b[j]
 return c
inv=[];p=[1]+[0]*N
for k in range(42):
 if k:
  for d in range(2*k,N+1):p[d]+=p[d-2*k]
 inv.append(p.copy())
lhs=[]
for parity in [0,1]:
 z=[0]*(N+1)
 for a in range(C+1):
  for j in range(C+1):
   base=mul(inv[a],inv[j])
   for s in range(C+1):
    e=a*a-a*j+j*j-j+2*s*s+2*s-2*s*j+parity*(2*s+1-j)
    assert e>=0
    if e>N:continue
    den=mul(base,inv[2*s+parity])
    for d in range(N+1-e):z[e+d]+=den[d]
 lhs.append(z)
# J3^3/(J1 J2^2 J6), expand every numerator and inverse geometric factor exactly.
r=[1]+[0]*N
for step,power in [(3,3),(1,-1),(2,-2),(6,-1)]:
 for d in range(step,N+1,step):
  for _ in range(abs(power)):
   if power>0:
    for k in range(N,d-1,-1):r[k]-=r[k-d]
   else:
    for k in range(d,N+1):r[k]+=r[k-d]
rhs=[]
for x,y in [(4,8),(2,10)]:
 theta=[0]*(N+1)
 for z in range(-C,C+1):
  e=x*z*(z+1)//2+y*z*(z-1)//2
  if 0<=e<=N:theta[e]+=1
 rhs.append([3*c for c in mul(r,theta)])
out=dict(degree_cap=N,index_cap=C,lhs=lhs,rhs=rhs,mismatch_degrees=[[d for d in range(N+1) if l[d]!=r[d]] for l,r in zip(lhs,rhs)])
(D/'outputs/nahm.json').write_text(json.dumps(out,indent=2)+'\n');print(out['mismatch_degrees'])
