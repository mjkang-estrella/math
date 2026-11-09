from itertools import product
from fractions import Fraction
from pathlib import Path
import json
L=Path(__file__).resolve().parent
out=[]
for ns,m in [([],4),([1],2),([2,2],2),([2,4],4),([2,2,2],2),([3,3],3),([2,3],6),([4,4],4)]:
 A=list(product(*[range(n) for n in ns]));ij=[(i,j) for i in range(len(ns)) for j in range(i+1,len(ns))]
 choices=[[v for v in range(m) if ns[i]*v%m==ns[j]*v%m==0] for i,j in ij]
 count=0;probs=set()
 for cs in product(*choices):
  def f(a,c):return sum(a[i]*c[j]*v for (i,j),v in zip(ij,cs))%m
  def b(a,c):return sum((a[i]*c[j]-a[j]*c[i])*v for (i,j),v in zip(ij,cs))%m
  for a,c in product(A,repeat=2):
   assert (f(a,c)-f(c,a))%m==b(a,c)
   for i,n in enumerate(ns):
    aa=list(a);aa[i]+=n;assert f(aa,c)==f(a,c)
    cc=list(c);cc[i]+=n;assert f(a,cc)==f(a,c)
   for d in A:
    ac=tuple((a[i]+c[i])%n for i,n in enumerate(ns))
    assert f(ac,d)==(f(a,d)+f(c,d))%m
  probs.add(str(Fraction(sum(b(a,c)==0 for a,c in product(A,repeat=2)),len(A)**2)));count+=1
 out.append(dict(cyclic_orders=ns,B_modulus=m,all_admissible_coefficient_arrays=count,probabilities=sorted(probs)))
# Exact free-cover count, A=C2^2, F=(Z/4)^4, B=C2; all A elements as generators.
A=list(product(range(2),repeat=2));F=list(product(range(4),repeat=4))
def p(x):return tuple(sum(x[i]*A[i][j] for i in range(4))%2 for j in range(2))
fib=[sum(p(x)==a for x in F) for a in A];assert fib==[64]*4
zeros=sum((p(x)[0]*p(y)[1]-p(x)[1]*p(y)[0])%2==0 for x,y in product(F,repeat=2))
assert Fraction(zeros,len(F)**2)==Fraction(5,8)
# Nonassociative S=F2^2: e0 e0=e1, e1 e0=e0, other basis products zero.
S=list(range(4));mul=lambda a,b: (((a&1)<<1)^((a>>1)&1)) if b&1 else 0
assert mul(mul(1,1),1)!=mul(1,mul(1,1))
T=list(product(S,repeat=2));zero=(0,0)
def circ(x,y):return (x[0]^y[0],x[1]^y[1]^mul(x[0],y[0]))
def inv(x):return(x[0],x[1]^mul(x[0],x[0]))
for x,y,z in product(T,repeat=3):assert circ(circ(x,y),z)==circ(x,circ(y,z))
for x in T:assert circ(x,inv(x))==circ(inv(x),x)==zero
for x,y in product(T,repeat=2):
 c=circ(circ(circ(inv(x),inv(y)),x),y)
 assert c==(0,mul(x[0],y[0])^mul(y[0],x[0]))
 assert all(circ(c,z)==circ(z,c) for z in T)
ps=Fraction(sum(mul(x,y)==mul(y,x) for x,y in product(S,repeat=2)),16)
pt=Fraction(sum(circ(x,y)==circ(y,x) for x,y in product(T,repeat=2)),256)
assert ps==pt
result=dict(status='PASS',triangular_cases=out,free_cover=dict(fibers=fib,probability='5/8'),nonassociative_reverse=dict(S_size=4,T_size=16,probability=str(ps)),scope='finite diagnostics only; universal proof in review.md')
(L/'checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
