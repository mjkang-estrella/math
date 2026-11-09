import math,json

def add(a,b):
 return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b): c[i+j]+=x*y
 return c
def pair(m,E):
 a,b=[2],[1,2]
 for _ in range(E): a,b=add(mul([0,1],a),b),add(mul([0,1,1],a),mul([0,1],b))
 for _ in range(m): a,b=add(mul([1,2],a),mul([2],b)),add(mul([0,2,2],a),mul([1,2],b))
 return a,b
def trim(a):
 while a and a[-1]==0:a.pop()
 return a
checks=0
for m in range(25):
 for E in range(25):
  e,r=divmod(E,2); out=[0]*(e+m+e+2)
  for i in range(m+e+2):
   k=2*i+(1-r); out[e+i]=2**k*math.comb(m+e+i+1,k)
  assert trim(pair(m,E)[0])==trim(out)
  checks+=1
print(json.dumps(dict(reduced_pair_binomial_checks=checks,all_ok=True)))
