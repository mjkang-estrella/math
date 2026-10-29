from pathlib import Path
from fractions import Fraction
from itertools import combinations
import json
P=Path(__file__).parent
N=60
s=[0]*(N+1);u=s.copy();v=s.copy();s[1]=1
A=[{} for _ in s];U=[{} for _ in s];V=[{} for _ in s]
A[1][0]=(0,1,0)
def get(tab,total,n,k):return tab[n].get(k,(total[n],0,0))
def mul(a,b,sa,sb):
 e,f,g=a;h,i,j=b
 return (e*h,f*sb+sa*i,g*sb+2*f*i+sa*j)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
for n in range(2,N+1):
 for i in range(1,n):
  j=n-i;u[n]+=((i==1)+v[i])*s[j];v[n]+=((i==1)+u[i])*s[j]
 s[n]=u[n]+v[n]
 for k in range(1-n,n):
  a=b=(0,0,0)
  for i in range(1,n):
   j=n-i
   def left(tab,total,z):return get(A,s,1,z) if i==1 else get(tab,total,i,z)
   sa=1 if i==1 else v[i]
   a=add(a,mul(left(V,v,k),get(A,s,j,k),sa,s[j]))
   sa=1 if i==1 else u[i]
   b=add(b,mul(left(U,u,k+j),get(A,s,j,k-i),sa,s[j]))
  U[n][k]=a;V[n][k]=b;A[n][k]=add(a,b)
# independent literal separable permutations by recursive direct/skew construction
T=[set() for _ in range(9)];T[1]={(1,)}
for n in range(2,9):
 for i in range(1,n):
  j=n-i
  for a in T[i]:
   for b in T[j]:
    T[n].add(a+tuple(x+i for x in b));T[n].add(tuple(x+j for x in a)+b)
for n in range(1,9):
 assert len(T[n])==s[n]
 for k in range(1-n,n):
  z=[sum(i-x==k for i,x in enumerate(t,1)) for t in T[n]]
  assert A[n][k]==(sum(x==0 for x in z),sum(z),sum(x*(x-1) for x in z))
known=[0,1,2,7,30,124,560,2610,12470,60955,302930,1528621,7790780,40202007,208787486,1094575377,5766892092,30609900691]
assert [A[n][0][0] for n in range(1,19)]==known
rows=[]
for n in [10,20,40,60]:
 e,f,g=A[n][0];mean=Fraction(f,s[n]);relvar=Fraction((g+f)*s[n]-f*f,f*f)
 rows.append(dict(n=n,s=s[n],empty=e,first=f,second_factorial=g,mean=str(mean),relative_variance=str(relvar),variance_bound_below_actual=relvar<Fraction(e,s[n])))
# scalar sum closure: U_0=V_0*E_0, so E_0=V_0/(1-V_0)
for n in range(2,N+1):assert U[n][0][0]==sum(V[i][0][0]*A[n-i][0][0] for i in range(2,n))
print(json.dumps({'status':'PASS','scope':'exact all-offset empty and first two factorial moments n<=60; independent literal sets n<=8; not a universal asymptotic proof','rows':rows},indent=2))
