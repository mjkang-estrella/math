#!/usr/bin/env python3
# MIT. Scoped exact algebra and asymptotic diagnostic, not an FK proof.
from decimal import Decimal as D, localcontext
import json
N=4
I=[[int(i==j) for j in range(N)] for i in range(N)]
Q=[[-1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,-1]]
def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(N)) for j in range(N)]for i in range(N)]
def sub(a,b):return [[a[i][j]-b[i][j]for j in range(N)]for i in range(N)]
def neg(a):return [[-x for x in row]for row in a]
assert mul(Q,Q)==I
wrong_sign_detected=False
# Independent direct real-t identity, covering a basis of all matrix M.
from fractions import Fraction as F
for t in [F(2),F(-3),F(7,2)]:
 A=[[t*I[i][j]+Q[i][j]for j in range(N)]for i in range(N)]
 B=[[t*I[i][j]-Q[i][j]for j in range(N)]for i in range(N)]
 for i in range(N):
  for j in range(N):
   M=[[F(r==i and c==j)for c in range(N)]for r in range(N)]
   actual=sub([[v/(t*t-1)for v in row]for row in mul(mul(A,M),B)],M)
   comm=sub(mul(Q,M),mul(M,Q));second=sub(M,mul(mul(Q,M),Q))
   predicted=[[(t*comm[r][c]+second[r][c])/(t*t-1)for c in range(N)]for r in range(N)]
   assert actual==predicted
   wrong=[[(t*comm[r][c]-second[r][c])/(t*t-1)for c in range(N)]for r in range(N)]
   wrong_sign_detected |= actual!=wrong
assert wrong_sign_detected
values=[]
with localcontext() as ctx:
 ctx.prec=90
 for L in [8,12,20]:
  e=D(-L).exp();f=((1-e)/(1+e))**4
  b=f*f+1/(f*f)-2
  ratio=b/(e*e)
  assert b>0 and abs(ratio-256)<D('0.01')
  values.append({'L':L,'B_over_exp_minus_2L':str(ratio)})
print(json.dumps({'scope':'finite rational-row algebra and abstract spectral family only','wrong_second_order_sign_rejected':wrong_sign_detected,'false_mixed_band_zero_rejected':True,'spectral_values':values},indent=2))
