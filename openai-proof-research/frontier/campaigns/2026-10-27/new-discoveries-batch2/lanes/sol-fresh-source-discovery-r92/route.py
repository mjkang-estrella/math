exec((__import__('pathlib').Path(__file__).parent/'check.py').read_text().split('out=[]')[0])
from functools import lru_cache
from itertools import product
@lru_cache(None)
def fcorner(p):
 if not p:return 1
 return sum(fcorner(p[:i]+((p[i]-1,) if p[i]>1 else ())+p[i+1:]) for i in range(len(p)) if i==len(p)-1 or p[i]>p[i+1])
@lru_cache(None)
def schur(p,m):
 if not p:return 1
 if m==0:return 0
 # interlacing subshape remaining after removing horizontal strip of letter m
 s=0
 for q in product(*(range(p[i+1] if i+1<len(p) else 0,p[i]+1) for i in range(len(p)))):
  q=tuple(x for x in q if x);s+=schur(q,m-1)
 return s

def insertion(w):
 rows=[]
 for x in w:
  for r in rows:
   j=next((j for j,y in enumerate(r) if y>x),len(r))
   if j==len(r):r.append(x);break
   r[j],x=x,r[j]
  else:rows.append([x])
 return tuple(tuple(r) for r in rows)
checks=0
for n in range(2,7):
 a,c=row(n)
 for m in range(1,5):
  literal=sum(insertion((1,)+w)==insertion(w+(1,)) for w in product(range(1,m+1),repeat=n))
  formula=sum(factorial(n)//hooks(p)*prod(m-1+j-i for i,r in enumerate(p[1:]) for j in range(r))//hooks(p[1:]) for p in partitions(n))
  assert literal==formula;checks+=1
n=10;a,c=row(n)
independent=[0]+[sum(fcorner(p)*schur(p[1:],m-1) for p in partitions(n)) for m in range(1,n)]
assert independent==c
# Exact route obstruction among actual shape components, after grouping all hooks.
obstructions=[]
for n in range(4,15):
 components=[('grouped_hooks',[0]+[comb(n-2,k-1) for k in range(1,n)])]
 for p in partitions(n):
  if len(p)<2 or p[1]<2:continue
  mu=p[1:];vals=[0]+[prod(m-1+j-i for i,r in enumerate(mu) for j in range(r))//hooks(mu) for m in range(1,n)]
  d=vals;v=[]
  while d:v.append(d[0]);d=[y-x for x,y in zip(d,d[1:])]
  assert all(x>=0 for x in v)
  components.append((p,v))
 for i,(p,u) in enumerate(components):
  for q,v in components[i+1:]:
   for k in range(1,n-1):
    cross=2*u[k]*v[k]-u[k-1]*v[k+1]-v[k-1]*u[k+1]
    if cross<0:
     obstructions.append({'n':n,'shape1':p,'shape2':q,'u':u,'v':v,'index':k,'mixed_LC_coefficient':cross});break
   if obstructions:break
  if obstructions:break
 if obstructions:break
import sympy as sp
x=sp.symbols('x');p=sum(row(6)[0][k]*x**(k-1) for k in range(1,6));st=sp.sturm(p,x)
(L/'route-results.json').write_text(json.dumps({'literal_word_checks':checks,'independent_n10_c':independent,'n10_a':a,'mixed_shape_obstruction':obstructions,'n6_reduced_polynomial':str(p),'n6_sturm':[str(v) for v in st],'n6_negative_real_roots':int(sp.Poly(p,x).count_roots(-sp.oo,0))},indent=2));print((L/'route-results.json').read_text())
