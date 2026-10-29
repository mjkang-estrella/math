import os,resource,signal,json,math
from fractions import Fraction as F
from pathlib import Path
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(40,40));signal.alarm(50)
b=Path(__file__).parent
# sparse Q[x,g2,g3]; all operations exact, no symbolic-library dependencies
one={(0,0,0):F(1)};x={(1,0,0):F(1)};g={(0,1,0):F(1)};h3={(0,0,1):F(1)}
def add(*ps):
 r={}
 for p in ps:
  for k,v in p.items():r[k]=r.get(k,F(0))+v
 return {k:v for k,v in r.items() if v}
def scale(p,a):return {k:v*a for k,v in p.items() if v*a}
def mul(p,q):
 r={}
 for k,v in p.items():
  for l,w in q.items():
   t=tuple(a+b for a,b in zip(k,l));r[t]=r.get(t,F(0))+v*w
 return {k:v for k,v in r.items() if v}
def diff(p,j):return {tuple(t-(i==j) for i,t in enumerate(k)):v*k[j] for k,v in p.items() if k[j]}
def delta(p):return add(scale(mul(h3,diff(p,1)),6),scale(mul(mul(g,g),diff(p,2)),F(1,3)))
h=add(scale(mul(mul(x,x),x),4),scale(mul(g,x),-1),scale(h3,-1));hp=diff(h,0)
def L(p):return add(mul(h,diff(diff(p,0),0)),scale(mul(hp,diff(p,0)),F(1,2)))
N=20
K=[(scale(one,2),{}),({},scale(one,-2)),(scale(g,F(1,6)),{})]
for n in range(3,N+3):
 K.append(tuple(scale(add(scale(mul(g,K[n-2][j]),2*n-3),scale(mul(h3,K[n-3][j]),2*n-4)),F(1,8*n-4)) for j in [0,1]))
def period(p):
 out=[{},{}]
 for (a,c,d),v in p.items():
  mon={(0,c,d):v}
  for j in [0,1]:out[j]=add(out[j],mul(mon,K[a][j]))
 return out
c={2:scale(g,F(1,20)),3:scale(h3,F(1,28))}
for n in range(4,N+2):
 c[n]=scale(add(*(mul(c[j],c[n-j]) for j in range(2,n-1))),F(3,(2*n+1)*(n-3)))
rows=[];P=x;odd=False;E=x
for m in range(1,N+1):
 direct=period(mul(mul(P,P),h) if odd else mul(P,P)); direct=[scale(q,F((-1)**(m-1),2)) for q in direct]
 ibp=[scale(q,F(1,2)) for q in period(mul(x,E))]
 assert direct==ibp
 if m==1:expected=[scale(g,F(1,12)),{}]
 else:expected=[scale(delta(c[m]),math.factorial(2*m-2)),scale(c[m],-2*m*math.factorial(2*m-2))]
 assert direct==expected,(m,direct,expected)
 assert all(v>0 for v in direct[0].values()) and all(v<0 for v in direct[1].values())
 rows.append({'m':m,'A':[[list(k[1:]),str(v)] for k,v in sorted(direct[0].items())],'B':[[list(k[1:]),str(-v)] for k,v in sorted(direct[1].items())]})
 P=add(mul(h,diff(P,0)),scale(mul(hp,P),F(1,2))) if odd else diff(P,0);odd=not odd;E=L(E)
# coefficient identity of classical heat bridge, independently as Laurent convolution
for k in range(1,N):
 val=scale(c[k+2],F(2*k+6)+F(2,2*k+3))
 for i in range(1,k):
  j=k-i
  val=add(val,scale(mul(c[i+1],c[j+1]),F(2)-F(2*i,2*j+1)))
 assert val==delta(c[k+1]),k
out={'status':'PASS','orders':N,'derivative_square_vs_IBP_vs_classical_bridge':True,'laurent_convolution_vs_delta':N-1,'finite_checks_not_proof':True,'rows':rows}
(b/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS: 20 literal derivative squares / IBP / heat bridge; 19 Laurent identities')
