# Exact polynomial-ring verification of the rational identity in ATTEMPTS.md.
def trim(p):
 while len(p)>1 and p[-1]==0:p.pop()
 return p
def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,v in enumerate(a):c[i]+=v
 for i,v in enumerate(b):c[i]+=v
 return trim(c)
def neg(a):return [-v for v in a]
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return trim(c)
def plus(x,y):return add(mul(x[0],y[1]),mul(y[0],x[1])),mul(x[1],y[1])
def times(x,y):return mul(x[0],y[0]),mul(x[1],y[1])
def same(x,y):return add(mul(x[0],y[1]),neg(mul(y[0],x[1])))==[0]
zero=([0],[1]);one=([1],[1]);v={5:(zero,one),4:(one,zero)}
for s in range(3,-1,-1):
 # q_(m-s)=(6-9/(m-s))q_(m-s-1)-(1-3/(m-s))q_(m-s-2)
 a=([-6*s-9,6],[-s,1]);b=([s+3,-1],[-s,1])
 v[s]=tuple(plus(times(a,v[s+1][j]),times(b,v[s+2][j])) for j in [0,1])
B0=[7,-53,122,-87,23,-2];D=[1]
for s in range(4):D=mul(D,[-s,1])
expected=[[496440,-412770,135851,-21003,1282],[-113400,88074,-27227,3933,-220]]
for j in [0,1]:
 result=zero
 for i,c in enumerate(B0):result=plus(result,times(([c],[1]),v[i][j]))
 assert same(result,(expected[j],D))
print('PASS exact symbolic rational-function identity, both independent scalar basis coefficients; no interpolation inference')
