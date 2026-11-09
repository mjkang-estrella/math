"""Independent root check: polynomial quotient arithmetic only, no symbolic algebra."""
import json
from pathlib import Path
R=Path(__file__).resolve().parent
g=[2,2,2,0,2,0,1,1]
def norm(a):
 a=[x%3 for x in a]
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b):
 return norm([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def neg(a):return norm([-x for x in a])
def rawmul(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 return norm(r)
def red(a):
 a=norm(a)
 while len(a)>=len(g):
  k=len(a)-len(g);c=a[-1]
  a=add(a,[0]*k+[-c*t for t in g])
 return a
def mul(a,b):return red(rawmul(a,b))
def power(a,k):
 r=[1]
 while k:
  if k%2:r=mul(r,a)
  a=mul(a,a);k//=2
 return r
x=[0,1];one=[1]
assert power(x,3**7)==x
assert [sum(c*z**i for i,c in enumerate(g))%3 for z in range(3)]==[2,1,1]
quot=[2,0,1,2,1]
assert rawmul(g,quot)==[1,1]+[0]*9+[1]
alpha=power(x,8)
assert alpha==[2,0,0,1,2,1,1]
assert power(alpha,5)==[2,1,2,2,2,1,2]
assert alpha not in ([0],[1])
U=add(one,neg(power(alpha,4)));V=add(one,neg(alpha))
assert U!=[0] and V!=[0]
assert add(x,power(x,11))==[2]
assert U==mul(power(x,2),V)
# Clear Eq12 by multiplying by alpha^2 U^9 V^9.
assert mul(mul(power(alpha,2),U),power(V,9))==mul(V,power(U,9))
assert power(alpha,(3**14-1)//8)==[1]
assert power(alpha,5)!=[1]
out={'status':'PASS','q':3,'n':14,'d':2,'irreducibility':'X^(3^7)=X mod g; degree 7 prime; no linear roots',
'alpha':alpha,'alpha_fifth':power(alpha,5),'R2':[2],
'equation12_cleared':True,'equation13':True,'nonzero_denominators':True,
'scope':'Independent finite field witness check; not novelty or substantive acceptance.'}
(R/'root-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
