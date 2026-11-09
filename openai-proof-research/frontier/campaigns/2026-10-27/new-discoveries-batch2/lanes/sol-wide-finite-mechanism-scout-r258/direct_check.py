from retrieve import *
mod=[2,2,2,0,2,0,1];N=7
# Independent quotient arithmetic uses Python lists and integers, not SymPy.
def add(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
def neg(a):return tuple(-x%3 for x in a)
zero=(0,)*N;one=(1,)+(0,)*(N-1);x=(0,1)+(0,)*(N-2)
def mul(a,b):
 c=[0]*(2*N-1)
 for i in range(N):
  for j in range(N):c[i+j]=(c[i+j]+a[i]*b[j])%3
 for i in range(2*N-2,N-1,-1):
  v=c[i]
  for j in range(N):c[i-N+j]=(c[i-N+j]-v*mod[j])%3
 return tuple(c[:N])
def power(a,e):
 r=one
 while e:
  if e&1:r=mul(r,a)
  a=mul(a,a);e//=2
 return r
assert power(x,3**7)==x
# No F3 root + Frobenius degree7 identity proves irreducibility (7 is prime).
assert all(sum((mod+[1])[i]*pow(t,i,3) for i in range(8))%3 for t in range(3))
alpha=power(x,8);R=add(x,power(x,11));T=add(add(one,alpha),add(power(alpha,2),power(alpha,3)))
assert power(x,2)==T
assert power(alpha,5)!=one
assert alpha!=zero and alpha!=one
assert power(alpha,4)!=one
assert power(R,3)==R
assert power(alpha,(3**14-1)//8)==one
assert power(x,3**14)==x
result={'modulus_ascending':mod+[1],'modulus_printed':'z^7+z^6-z^4-z^2-z-1','x':x,'alpha_x8':alpha,'R2_x':R,'alpha5':power(alpha,5),'eq12_LHS':None,'all_assertions':True,'independent_arithmetic':'integer tuples over F3, Rabin prime-degree criterion; no symbolic library','field':'F_(3^7) embedded in F_(3^14)'}
U=add(one,neg(power(alpha,4)));V=add(one,neg(alpha))
inv=lambda a:power(a,3**7-2)
lhs=mul(U,inv(power(U,9)));rhs=mul(inv(power(alpha,2)),mul(V,inv(power(V,9))))
assert lhs==rhs
result['eq12_LHS']=lhs;result['eq12_RHS']=rhs
(L/'independent-checks.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
