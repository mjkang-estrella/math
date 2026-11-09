from math import comb
import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def add(*ps):
 c=[0]*max(map(len,ps))
 for p in ps:
  for i,v in enumerate(p):c[i]+=v
 return c
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def scale(a,v):return [v*x for x in a]
def eq(a,b):return add(a,scale(b,-1))==[0]*max(len(a),len(b))
R=40;a=[0,3,2];b=[0,1,3,3,1];T=[[1]]
for r in range(1,R+3):
 p=mul(a,T[-1])
 for i in range(r-1):p=add(p,mul(b,mul(T[i],T[r-2-i])))
 T.append(p)
M=[add(*[scale(T[j],comb(r,j)) for j in range(r+1)]) for r in range(R+3)]
G=[]
for j in range(R):G.append(add(mul([1,2,1],add(T[j],T[j+1])),mul([0,-1,0,1],add(T[j],scale(T[j+1],2),T[j+2]))))
for r in range(1,R+1):
 lhs=mul([1,2,1],add(mul([1,1],M[r]),mul([0,-1,1],M[r+1])))
 rhs=mul([1,1],add(*[scale(G[j],comb(r-1,j)) for j in range(r)]))
 assert eq(lhs,rhs),r
print('PASS polynomial Newton decline identity r=1..40, full class k=3..42')
data=json.loads((D/'results-exact.json').read_text());q=data['q'];N=250
P=[[0]*(N+1) for _ in range(86)];P[0][0]=1;P[1]=q
for j in range(2,len(P)):
 for n in range(N+1):P[j][n]=P[j-1][n]-(P[j-1][n-1]+P[j-2][n-1] if n else 0)
for r,g in enumerate(G):
 coeff=[sum(c*P[j][n] for j,c in enumerate(g) if j<=n) for n in range(N+1)]
 assert min(coeff)>=0,(r,next((n for n,x in enumerate(coeff) if x<0),None))
 print(json.dumps({'G':r,'composed_checked_through':250,'min':min(coeff)}))
# Exact rational-recurrence consequences for first decline.
A=lambda m:1282*m**4-21003*m**3+135851*m**2-412770*m+496440
B=lambda m:-220*m**4+3933*m**3-27227*m**2+88074*m-113400
for n in range(8,N+1):
 m=n-2;den=m*(m-1)*(m-2)*(m-3)
 assert den*(data['rows'][n][2]-data['rows'][n][3])==A(m)*q[m-4]+B(m)*q[m-5]
print('PASS first-decline exact recurrence certificate n=8..250')
print('PASS ratio lower bound seed',q[11],q[10],q[11]>=5*q[10])
