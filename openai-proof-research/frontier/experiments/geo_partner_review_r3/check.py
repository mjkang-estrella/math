"""Independent exact checks; no imports from earlier research scripts."""
from fractions import Fraction as F
from itertools import product, combinations_with_replacement, permutations

def rank(rows):
 piv={}
 for row in rows:
  v={k:F(x) for k,x in row.items() if x}
  while v:
   j=min(v)
   if j not in piv:
    c=v[j];piv[j]={k:x/c for k,x in v.items()};break
   c=v[j]
   for k,x in piv[j].items():
    v[k]=v.get(k,F(0))-c*x
    if not v[k]:del v[k]
 return len(piv)

# Augmentation-torus characters; works for both possible cubic Galois groups.
for group in ('C3','S3'):
 ps=[(0,1,2),(1,2,0),(2,0,1)] if group=='C3' else list(permutations(range(3)))
 orbit=[tuple((0,1,-1)[i] for i in p) for p in ps]
 assert rank([dict(enumerate(x)) for x in orbit])==2
 killed=[s for s in product((-1,1),repeat=3) if all(sum(a*b for a,b in zip(s,o))==0 for o in orbit)]
 assert killed==[(-1,-1,-1),(1,1,1)]
 print(group,'central torus rank 2; trivial coherent characters:',killed)

# Independent Phi tensor, exterior derivatives, symplectic-normalized deformation basis.
def eps(a,b):return (a==0 and b==1)-(a==1 and b==0)
def bits(x):return ((x>>2)&1,(x>>1)&1,x&1)
def omv(x,y):
 a,b=bits(x),bits(y);return eps(a[0],b[0])*eps(a[1],b[1])*eps(a[2],b[2])
def om(x,y):
 if x<8 and y<8:return omv(x,y)
 if x<8 or y<8:return 0
 r,a=divmod(x-8,2);s,b=divmod(y-8,2)
 return eps(a,b) if r//2==s//2 and r!=s else 0
P=list(range(4))+[8,10,12,13,18,19]
Q=[i for i in range(20) if i not in P]
dual=[]
for p in P:
 matches=[(q,om(p,q)) for q in Q if om(p,q)]
 assert len(matches)==1;dual.append(matches[0])
assert len(set(q for q,c in dual))==10

def canonical(t):
 if len(set(t))!=len(t):return None,0
 return tuple(sorted(t)),(-1)**sum(t[i]>t[j] for i in range(len(t)) for j in range(i+1,len(t)))

def tensor(a,b):
 out={}
 for v in range(8):
  x,y,z=bits(v)
  # omega-dual d satisfies omega(d,v)=1.
  dv=7-v;coeff=omv(dv,v)
  for weight,slots in [(a,(8+x,12+y,16+z)),(b,(10+x,14+y,18+z))]:
   key,sign=canonical((dv,)+slots)
   out[key]=out.get(key,F(0))+coeff*weight*sign
 return {k:x for k,x in out.items() if x}

def derivative(t, i,j):
 # Symmetric matrix unit in coordinates omega(P_i,xi P_j).
 action={P[j]:dual[i]}
 if i!=j:action[P[i]]=dual[j]
 result={}
 for term,c in t.items():
  for k,x in enumerate(term):
   if x not in action:continue
   q,coeff=action[x]
   key,sign=canonical(term[:k]+(q,)+term[k+1:])
   if sign:result[key]=result.get(key,F(0))+c*coeff*sign
 return result
for a,b in [(1,1),(1,-1),(1,3),(2,5),(1,0),(0,1)]:
 t=tensor(F(a),F(b))
 assert all(sum(x in P for x in term)==2 for term in t)
 r=rank([derivative(t,i,j) for i,j in combinations_with_replacement(range(10),2)])
 print('Phi coefficients',(a,b),'rank',r,'kernel',55-r)
 if a*b:assert r==54

# Sign/dimension checks of all eight tensor pieces.
for signs in product((1,-1),repeat=3):
 types={}
 for first in (0,1):
  p=first+(1+signs[1])//2+(1-signs[2])//2;types[(p,3-p)]=4
 coherent=len(set(signs))==1
 print('piece',signs,'types',types,'coherent',coherent)

# Local-degree obstruction: a cubic completion partition contains at most one quadratic factor.
for part in [(3,),(2,1),(1,1,1)]:assert sum(d==2 for d in part)<=1
print('All cubic local degree partitions checked; at most one forbidden quadratic completion.')
