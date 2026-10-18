#!/usr/bin/env python3
"""Exact Q(zeta_12) diagnostics; finite examples, not a universal proof."""
import itertools,json
Z=(0,0,0,0)
def c(n): return (n,0,0,0)
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def neg(a): return tuple(-x for x in a)
def sub(a,b): return add(a,neg(b))
def mul(a,b):
 r=[0]*7
 for i,x in enumerate(a):
  for j,y in enumerate(b): r[i+j]+=x*y
 for k in range(6,3,-1):
  r[k-2]+=r[k];r[k-4]-=r[k]
 return tuple(r[:4])
def sm(xs):
 r=Z
 for x in xs:r=add(r,x)
 return r
P=[c(1)]
for _ in range(11): P.append(mul(P[-1],(0,1,0,0)))
def rt(e):return P[e%12]
def conj(a):return sm(mul(c(x),rt(-i)) for i,x in enumerate(a))
def abs2(a):return mul(a,conj(a))
def mm(A,B):return [[sm(mul(x,y) for x,y in zip(row,col)) for col in zip(*B)] for row in A]
def adj(A):return [[conj(x) for x in col] for col in zip(*A)]
def scale(A,n):return [[mul(c(n),x) for x in row] for row in A]
def ident(n,s=1):return [[c(s if i==j else 0) for j in range(n)] for i in range(n)]
def phase(E):return [[rt(e) for e in row] for row in E]
subs=list(itertools.combinations(range(6),3));reps=[I for I in subs if 0 in I]
charges=[[1 if i in I else -1 for i in range(6)] for I in subs]
def numerators(E):
 return [sm(abs2(sm(rt(q*sum(a[i]*E[i][j] for i in range(6))) for j in range(6))) for a in charges) for q in (1,3)]
def adjexp(E):return [[-E[j][i] for j in range(6)] for i in range(6)]
def m2(E):
 total=sum(map(sum,E));assert total%2==0
 return [[sm([rt(sum(E[i][j] for i in range(6) for j in range(6) if ((i in I)==(j in S)))-total//2),rt(-sum(E[i][j] for i in range(6) for j in range(6) if ((i in I)==(j in S)))+total//2)]) for S in reps] for I in reps]
def check_m(E):
 assert mm(adj(phase(E)),phase(E))==ident(6,6)
 n=numerators(E);nt=numerators(adjexp(E));assert n[0]==nt[0]==Z
 M=m2(E);assert m2(adjexp(E))==list(map(list,zip(*M)))
 r=[sm(row) for row in M];co=[sm(col) for col in zip(*M)]
 assert n[1]==mul(c(18),sm(mul(x,x) for x in r))
 assert nt[1]==mul(c(18),sm(mul(x,x) for x in co))
 return {'first_numerators':[n[0],nt[0]],'third_numerators':[n[1],nt[1]],'row_sums_2M':r,'column_sums_2M':co}
H=[[6*(i//3)*(j//3)+4*(i%3)*(j%3) for j in range(6)] for i in range(6)]
K=[[3*(i//3)+6*(i//3)*(j//3)+4*(i%3)**2+4*(i%3)*(j%3) for j in range(6)] for i in range(6)]
assert all(abs2(x)==c(6) for row in mm(adj(phase(H)),phase(K)) for x in row)
Hcube=phase([[3*e for e in row] for row in H])
assert Hcube[0]==Hcube[1]==Hcube[2] and Hcube[3]==Hcube[4]==Hcube[5]
assert Hcube[0]!=Hcube[3] and mm(adj(Hcube),Hcube)!=ident(6,6)
D=[]
for i in range(6):
 for j in range(6):
  if i!=j:D.append([int(k==i)-int(k==j) for k in range(6)])
def gram(E):
 V=[[rt(sum(a[i]*E[i][k] for i in range(6))) for k in range(6)] for a in D]
 return mm(V,adj(V))
SH,SK=gram(H),gram(K)
assert mm(SH,SH)==scale(SH,36) and mm(SK,SK)==scale(SK,36)
assert mm(SH,SK)==[[Z]*30 for _ in range(30)]
Q=[[sub(sub(ident(30,36)[i][j],SH[i][j]),SK[i][j]) for j in range(30)] for i in range(30)]
assert mm(Q,Q)==scale(Q,36) and sm(Q[i][i] for i in range(30))==c(720)
a=[-2,0,0,0,1,1]
sums=[sm(rt(sum(a[i]*E[i][k] for i in range(6))) for k in range(6)) for E in (H,K)]
assert sums==[c(6),(0,0,6,0)]
examples={'tensor_H':check_m(H),'tensor_K':check_m(K)}
for t1,t2 in [(1,3),(1,2),(2,5)]:
 E=[[6*(i//3)*(j//3)+4*(i%3)*(j%3)+(i//3)*[0,t1,t2][j%3] for j in range(6)] for i in range(6)]
 # A global phase can make sum E even without changing M up to sign.
 if sum(map(sum,E))%2: raise AssertionError('delta outside zeta12 field')
 examples[f'Fourier_deformation_{t1}_{t2}']=check_m(E)
# Charge-order witness is an integer exponent matrix, not a numerical approximation.
a=[3,3,3,-3,-3,-3];b=[-3,3,3,3,-3,-3]
A=[[0]*6 for _ in range(6)]
for i in range(6):A[i][0]+=a[i];A[i][1]-=a[i]
for j in range(6):A[2][j]-=b[j];A[3][j]+=b[j]
assert all(sum(row)==0 for row in A) and all(sum(col)==0 for col in zip(*A))
assert sum(max(x,0) for row in A for x in row)==36
print(json.dumps({'status':'PASS','field':'Q(zeta_12), zeta^4-zeta^2+1=0','complement_rank':20,'order_two_unnormalized_sums':sums,'order36_witness':A,'examples':examples,'scope':'Finite exact diagnostics only; T266 remains unresolved.'},indent=2))
