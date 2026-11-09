import resource,os,pathlib,json,itertools,math
from fractions import Fraction as F
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);D=pathlib.Path(__file__).resolve().parents[1];out=[]
for m,poly in [(2,7),(3,11),(4,19),(5,37)]:
 n=(1<<m)-1
 def mul(a,b):
  z=0
  while b:
   if b&1:z^=a
   b>>=1;a<<=1
   if a>>m:a^=poly
  return z
 powers=[1]
 for i in range(n-1):powers.append(mul(powers[-1],2))
 assert len(set(powers))==n
 for t in range(1,(1<<m)//2+1):
  rows=[]
  for j in range(1,2*t-1):
   for bit in range(m):rows.append(sum(((powers[(j*i)%n]>>bit)&1)<<i for i in range(n)))
  piv=[];r=0
  for c in range(n):
   z=next((j for j in range(r,len(rows)) if rows[j]>>c&1),None)
   if z is None:continue
   rows[r],rows[z]=rows[z],rows[r]
   for j in range(len(rows)):
    if j!=r and rows[j]>>c&1:rows[j]^=rows[r]
   piv.append(c);r+=1
  free=[c for c in range(n) if c not in piv];basis=[(1<<c)|sum(((rows[j]>>c)&1)<<v for j,v in enumerate(piv)) for c in free];dim=len(basis)
  if dim>19:out.append({'m':m,'t':t,'dimension':dim,'skipped':'codeword cap 2^19'});continue
  W=[0]*(n+2);word=0;prev=0
  for z in range(1<<dim):
   gray=z^(z>>1)
   if z:word^=basis[(gray^prev).bit_length()-1]
   prev=gray;w=word.bit_count();W[w+(w%2)]+=1
  dp=1
  while dp<2*t:dp*=2
  s=(n+1)//dp
  # Compute formal s-th root through degree 2n+2 using f'=g^(s-1) s g',
  # equivalently W*g'=W'*g/s. This exact recurrence uses only rational arithmetic.
  g=[F(1)]
  for k in range(1,2*(n+1)+1):
   val=sum(F(j)*W[j]*g[k-j] for j in range(1,min(k,len(W)-1)+1))/s
   val-=sum(F(k-j)*W[j]*g[k-j] for j in range(1,min(k,len(W)-1)+1))
   g.append(val/k)
  bad=[(i,str(v)) for i,v in enumerate(g) if v.denominator!=1]
  row={'id':379269,'m':m,'t':t,'designed_distance':2*t-1,'primitive_polynomial_bits':poly,'dimension':dim,'codewords':1<<dim,'root_exponent':s,'root_checked_through_degree':2*(n+1),'weight_enumerator':W,'nonintegral_coefficients':bad};out.append(row);print(json.dumps(row),flush=True)
  (D/'outputs/bch-search.json').write_text(json.dumps(out,indent=2))
