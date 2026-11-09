# Reduce q powers using q^2=(1-t)q-t. Return coefficient lists A(t)+B(t)q.
def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,v in enumerate(a):c[i]+=v
 for i,v in enumerate(b):c[i]+=v
 return c
def scale(a,v):return [v*x for x in a]
p=[([1],[0]),([0],[1])]
for i in range(2,8):
 a,b=p[-1];p.append(([0]+scale(b,-1),add(a,add(b,[0]+scale(b,-1)))))
for name,C in [('rise',[-1,-1]),('D2',[1,2,-1,-3,2,5,2])]:
 if name=='rise':continue
 A=[0];B=[0]
 for i,c in enumerate(C):A=add(A,scale(p[i][0],c));B=add(B,scale(p[i][1],c))
 print(name,A,B)
from fractions import Fraction as F
from math import prod
def lin(m):
 v={m-5:(F(0),F(1)),m-4:(F(1),F(0))}
 for i in range(m-3,m+1):v[i]=tuple(F(6*i-9,i)*v[i-1][j]-F(i-3,i)*v[i-2][j] for j in [0,1])
 return [sum(B[i]*v[m-i][j] for i in range(6))*prod(range(m-3,m+1)) for j in [0,1]]
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def interp(vals):
 P=[F(0)]
 for x,y in vals:
  p=[y]
  for a,b in vals:
   if a!=x:p=scale(mul(p,[-a,1]),F(1,x-a))
  P=add(P,p)
 return P
AB=[interp([(m,lin(m)[j]) for m in range(6,12)]) for j in [0,1]]
print('AB',AB)
for j in [0,1]:assert all(sum(c*m**i for i,c in enumerate(AB[j]))==lin(m)[j] for m in range(12,40))
print('5A+B',add(scale(AB[0],5),AB[1]))
from math import comb
for name,p in [('A',AB[0]),('B',AB[1]),('5A+B',add(scale(AB[0],5),AB[1]))]:
 s=[sum(p[i]*comb(i,j)*20**(i-j) for i in range(j,len(p))) for j in range(len(p))]
 print(name,'at m=20+x',s)
