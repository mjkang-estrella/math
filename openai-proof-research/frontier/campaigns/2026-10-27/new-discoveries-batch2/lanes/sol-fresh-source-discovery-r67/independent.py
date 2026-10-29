import pathlib,json,math
from fractions import Fraction as F
P=pathlib.Path(__file__).resolve().parent
from routes import add,mul,shift,A,g,fac
# Independent Euler-product construction in two variables, using rising factorials.
M=16
B=[[F(0)] for _ in range(M+1)];B[0]=[F(1)]
for k in range(1,M+1):
 c=[[F(1)]]
 for r in range(1,M//k+1):
  c.append([v/r for v in mul(c[-1],[F(r-1),F(k)])])
 C=[[F(0)] for _ in range(M+1)]
 for n in range(M+1):
  for r in range(n//k+1):C[n]=add(C[n],mul(B[n-k*r],c[r]))
 B=C
for n in range(M+1):
 b=B[n]+[F(0)]*max(0,len(A[n])-len(B[n]))
 assert [v*fac[n] for v in b[:n+1]]==A[n]
def val(a,x):
 r=F(0)
 for v in reversed(a):r=r*x+v
 return r
def delta(n,x):return val(A[n],x)**(n+1)*(n+1)**n-fac[n]*val(A[n+1],x)**n
# Independent scalar source recursion and exact source inequalities.
points=[F(1),F(101,100),F(5,4),F(3,2),F(2),F(5),F(501,100),F(6),F(10),F(100)]
count=0
for x in points:
 p=[F(1)]
 for n in range(1,102):p.append(x/n*sum(g[k]*p[n-k] for k in range(1,n+1)))
 for n in range(1,101):
  assert p[n]*fac[n]==val(A[n],x)
  if n>=6 or x>5:
   assert p[n]**(n+1)>p[n+1]**n
   count+=1
# Independent binomial shift identity (not Horner).
for n in range(1,20):
 d=add([v*(n+1) for v in mul([j*v for j,v in enumerate(A[n])][1:],A[n+1])],mul(A[n],[j*v for j,v in enumerate(A[n+1])][1:]),-n)
 assert shift(d,1)[:len(d)]==[sum(d[k]*math.comb(k,j) for k in range(j,len(d))) for j in range(len(d))]
# Show a positivity-only derivative route is false for an admissible arithmetic input.
p=[F(0),F(1)];q=[F(0),F(5),F(1,2)];r=[F(0),F(1,3),F(5),F(1,6)]
der=lambda a:[j*v for j,v in enumerate(a)][1:]
w=3*val(der(q),F(1))*val(r,F(1))-2*val(q,F(1))*val(der(r),F(1))
assert w==F(-121,6)
assert val(q,F(1))**3>val(r,F(1))**2
# Actual source derivative search below the requested threshold, no floating signs.
negative=[];samples=0
for n in range(1,51):
 d=add([v*(n+1) for v in mul(der(A[n]),A[n+1])],mul(A[n],der(A[n+1])),-n)
 for x in [F(1,100),F(1,20),F(1,10),F(1,5),F(1,2),F(3,4)]:
  v=val(d,x);samples+=1
  if v<0:negative.append({'n':n,'x':str(x),'value':str(v)})
obj={'euler_product_coefficient_rows':M+1,'exact_source_inequalities':count,'scalar_row_checks':100*len(points),'independent_shift_rows':19,'generic_derivative_obstruction':str(w),'below_threshold_samples':samples,'below_threshold_negative':negative}
(P/'independent.json').write_text(json.dumps(obj,indent=2));print(json.dumps(obj))
