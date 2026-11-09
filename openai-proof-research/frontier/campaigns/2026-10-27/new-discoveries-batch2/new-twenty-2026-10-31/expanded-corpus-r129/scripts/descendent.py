import math,json
from fractions import Fraction
P=1000000007;N=30
B=[Fraction(1)]
for m in range(1,N+2):B.append(-sum(Fraction(math.comb(m+1,j))*B[j] for j in range(m))/(m+1))
def mod(x):return x.numerator%P*pow(x.denominator,-1,P)%P
const=[0]+[mod(-(1-Fraction(1,2**l))*B[l+1]/(l+1)) for l in range(1,N)]
def partitions(n,top=None):
 if n==0:yield ();return
 for a in range(min(n,top or n),0,-1):
  for x in partitions(n-a,a):yield (a,)+x
values=[]
for d in range(N+1):
 vs=[]
 for lam in partitions(d):
  v=const.copy()
  for i,x in enumerate(lam,1):
   a=(2*x-2*i+1)*pow(2,-1,P)%P;b=(1-2*i)*pow(2,-1,P)%P;aa=bb=1
   for l in range(1,N):aa=aa*a%P;bb=bb*b%P;v[l]=(v[l]+aa-bb)%P
  vs.append(v)
 values.append(vs)
# Common Euler-product normalization is invertible; omitted for rank only.
for k in range(2,N+1,2):
 dim=sum(1 for a in range(k//2+1) for b in range(k//4+1) for c in range(k//6+1) if 2*a+4*b+6*c==k)
 piv={};tried=0;chosen=[]
 for parts in partitions(k):
  if min(parts)<2:continue
  exps=[a-1 for a in parts];v=[]
  for vs in values:
   total=0
   for row in vs:
    prod=1
    for e in exps:prod=prod*row[e]%P
    total+=prod
   v.append(total%P)
  tried+=1
  for j in sorted(piv):
   q=v[j]
   if q:v=[(a-q*b)%P for a,b in zip(v,piv[j])]
  j=next((j for j,a in enumerate(v) if a),None)
  if j is not None:
   z=pow(v[j],-1,P);piv[j]=[a*z%P for a in v];chosen.append(parts)
  if len(piv)==dim:break
 print(json.dumps({'weight':k,'coefficients_d':N,'prime':P,'qbracket_model_rank':len(piv),'QM_dimension':dim,'columns_tried':tried,'basis_parts':chosen,'full_rank':len(piv)==dim}),flush=True)
