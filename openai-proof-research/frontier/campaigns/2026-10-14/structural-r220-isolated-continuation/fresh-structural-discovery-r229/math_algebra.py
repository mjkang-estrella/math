"""Finite exact coefficient checks; supplementary to the author proof, not a proof gate."""
from fractions import Fraction as F
from pathlib import Path
import json
R=Path(__file__).resolve().parent
c=[F(9,2),F(7,2),F(33,7)]
v=[F(1),F(1),F(110,147)]
ell=[F(308,550),F(132,550),F(147,550)]
def V(z):
 a,b,d=z
 return [a*(1+b-a),b*(9+a+F(12,11)*b*d-9*b),(11-d)*a-8*d+b*d*(1-d/11)]
def along(z,t):return V([a+t*b for a,b in zip(c,z)])
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b)))for j in range(len(b[0]))]for i in range(len(a))]
assert V(c)==[0]*3
J=[[F(0)]*3 for _ in range(3)]
for j in range(3):
 e=[F(i==j)for i in range(3)]
 u,w,x,y=along(e,F(1,2)),along(e,F(-1,2)),along(e,F(1)),along(e,F(-1))
 for i in range(3):J[i][j]=(8*(u[i]-w[i])-(x[i]-y[i]))/6
assert J==[[F(-9,2),F(9,2),F(0)],[F(7,2),F(-27,2),F(147,11)],[F(44,7),F(132,49),F(-12)]]
assert mul(J,[[x]for x in v])==[[0],[0],[0]] and mul([ell],J)==[[0,0,0]] and dot(ell,v)==1
K=[[J[i][j]+15*F(i==j) for j in range(3)]for i in range(3)]
assert mul(J,mul(K,K))==[[0]*3 for _ in range(3)]
assert sum(J[i][i]for i in range(3))==-30
minors=sum(J[i][i]*J[j][j]-J[i][j]*J[j][i]for i in range(3)for j in range(i+1,3));assert minors==225
quad=[(x+y)/2 for x,y in zip(along(v,1),along(v,-1))];assert quad==[F(0),F(20,7),F(-2530,3087)]
a=dot(ell,quad);assert a==F(7,15)
f_log=-1/a;p_log=(c[2]*v[1]+c[1]*v[2])/a
assert f_log==F(-15,7) and p_log==F(110,7)
assert 8*f_log+F(12,11)*p_log==0
assert f_log+p_log/11==F(-5,7)
assert F(1,10)-F(1,11)==F(1,110)
# Algebraic equilibrium identity at rational test points supplements its explicit expansion in the proof.
for A in [F(5,2),F(3),F(4),F(9,2)]:
 B=A-1;D=11*(4*A-9)/(6*(A-1))
 assert V([A,B,D])==[0,0,55*(2*A-9)**2/(36*(A-1))]
record={'description':'Exact finite algebra checks, not independent correctness/contribution review','derived_J':J,'quadratic_at_null':quad,'neutral_drift':a,'log_exponents':[f_log,p_log],'volume_integral':F(1,110),'status':'all listed rational identities agree'}
(R/'math-algebra-output.json').write_text(json.dumps(record,default=str,indent=2)+'\n')
print(json.dumps(record,default=str))
