from fractions import Fraction as Q
from math import isqrt
import resource
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
def p(a,x):return sum((x-a*z)//2+1 for z in range(x//a+1))
def forms(a):
 out=[]
 for i in range(2*a):
  c=p(a,i); b=p(a,2*a+i)-a-c
  assert all(p(a,2*a*n+i)==a*n*n+b*n+c for n in range(5))
  out.append((i,b,c,Q(c)-Q(b*b,4*a)))
 return out
for a in range(3,101):
 for b in range(a+1,201):
  if isqrt(a*b)**2!=a*b:continue
  aa=forms(a);bb=forms(b);same=[(x,y) for x in aa for y in bb if x[3]==y[3]]
  print(a,b,'shared constants',len(same),'sample',same[:1])
  if not same: print('FINITE CANDIDATE',a,b);raise SystemExit
