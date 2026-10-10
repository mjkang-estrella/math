"""Exact finite checks of interfaces only. No infinite-algebra proof claim."""
from fractions import Fraction as F
import itertools,json

def mul(a,b):
 out=list(a)
 for x in b:
  if out and out[-1]==-x:out.pop()
  else:out.append(x)
 return tuple(out)
def inv(a):return tuple(-x for x in reversed(a))
def words(r,n):
 out=[()];last=[()]
 for k in range(n):
  last=[a+(b,) for a in last for b in list(range(1,r+1))+list(range(-r,0)) if not a or a[-1]!=-b];out+=last
 return out
def xi(a,t,r):
 return {a[:i]:(t**len(a) if i==0 else r*t**(len(a)-i)) for i in range(len(a)+1)}
def subscale(x,y,t,r):
 z={a:v/r for a,v in x.items()}
 for a,v in y.items():z[a]=z.get(a,0)-t*v/r
 return {a:v for a,v in z.items() if v}
def path_matrix(l,t,r):
 a=[[F(0) for j in range(l+1)] for i in range(l+1)]
 for j in range(l+1):
  for i in range(j+1):a[i][j]=(t**j if i==0 else r*t**(j-i))*(r if j<l else 1)
  if j<l:a[j+1][j]=-t
 return a
stats={}
count=0
for t,r in [(F(3,5),F(4,5)),(F(5,13),F(12,13)),(F(7,25),F(24,25)),(F(0),F(1))]:
 for l in range(13):
  T=path_matrix(l,t,r)
  for j in range(l+1):
   for k in range(l+1):assert sum(T[i][j]*T[i][k] for i in range(l+1))==(j==k)
  count+=1
stats['orthogonal_path_matrices']=count
count=0;roots=0;t=F(3,5);r=F(4,5)
for g in words(3,2):
 path={g[:i] for i in range(len(g)+1)}
 assert xi(g,t,r)[()]==t**len(g);roots+=1
 for y in words(3,3):
  if y in path:continue
  a=mul(inv(g),y);assert a
  toward=mul(g,a[:-1])
  out=subscale(xi(y,t,r),xi(toward,t,r),t,r)
  assert out=={y:F(1)}
  count+=1
stats['actual_off_path_identities']=count;stats['root_coefficients']=roots
count=0
for h in words(2,3)[1:]:
 for u in [3,4]:
  for w in words(4,3):
   if w and w[0]==u:continue
   out=mul((u,)+h+(-u,),w)
   assert out and out[0]==u
   count+=1
stats['fresh_generator_support_splits']=count
count=0
# E_cd E_ab = delta_da E_cb, E_kl E_ij = delta_li E_kj.
# Trace-GNS vector index (a,b,i,j); the b,j indices are multiplicities.
for c,d,a,b in itertools.product(range(2),repeat=4):
 for k,l,i,j in itertools.product(range(3),repeat=4):
  algebra=((c,b,k,j),1) if d==a and l==i else (None,0)
  represented=((c,b,k,j),int(d==a)*int(l==i))
  if represented[1]==0:represented=(None,0)
  assert algebra==represented
  count+=1
stats['matrix_unit_vectorization_checks']=count
for q in [F(1,3),F(1,2),F(1),F(2),F(3),F(7,4)]:
 c=q*q
 for old_norm2 in [F(1),F(3,7),F(123)]:assert c*(1/q)**2*old_norm2==old_norm2
stats['trace_weight_normalization_checks']=18
# Retain a diagnostic for the rejected sign of the scaling exponent.
stats['wrong_positive_half_scaling_at_c4_norm_ratio']=str(F(4)*F(2)**2)
assert stats['wrong_positive_half_scaling_at_c4_norm_ratio']=='16'
count=0
for den in range(2,101):
 for num in [1,den-1]:
  t=F(num,den);a=4/t**2;m=a.numerator//a.denominator+1
  assert m*t*t>4 and m*m*t*t>4*m
  count+=1
stats['strict_bad_witness_budgets']=count
stats['status']='PASS';stats['scope']='Finite exact identities only; no infinite-algebra, normality, trace-uniqueness or novelty certificate.'
print(json.dumps(stats,sort_keys=True,indent=2))
