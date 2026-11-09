import itertools,json

def mul(a,b,M):
 c=[0]*(M+1)
 for i,x in enumerate(a):
  for j,y in enumerate(b[:M+1-i]):c[i+j]+=x*y
 return c
checks=0
for n in range(3,11):
 M=2*n
 for bits in itertools.product(range(2),repeat=n):
  s={i for i,b in enumerate(bits) if b}
  if any((v+1)%n in s for v in s):continue
  E=s|{(v+1)%n for v in s}
  for z in [-2,0,1,2,3]:
   d=[1];p=[1]+[0]*M;chips=[1]
   for v in range(n):
    g=[1,-z**v]
    d=mul(d,g,M)
    if v in E:p=mul(p,g,M)
    else:chips=mul(chips,[z**(v*a) for a in range(M+1)],M)
   assert mul(d,chips,M)==p
   checks+=M+1
print(json.dumps({'per_matching_geometric_coefficients':checks,'status':'PASS'}))
# Independent literal enumeration against the exact-total matching sum.
checks2=0
for n in range(3,6):
 for m in range(5):
  for z in [1,-1]:
   literal=0
   for x in itertools.product(range(m+1),repeat=n):
    if sum(x)!=m:continue
    for q in itertools.product(range(2),repeat=n):
     if any(q[v] and not q[(v+1)%n] and x[v]==x[(v+1)%n]==0 for v in range(n)):continue
     literal+=z**(sum(v*x[v] for v in range(n))+sum(1-b for b in q))
   expansion=0
   for bits in itertools.product(range(2),repeat=n):
    s={i for i,b in enumerate(bits) if b}
    if any((v+1)%n in s for v in s):continue
    E=s|{(v+1)%n for v in s}
    a=[1]
    for v in range(n):
     if v not in E:a=mul(a,[z**(v*j) for j in range(m+1)],m)
    expansion+=(-z)**len(s)*(1+z)**(n-2*len(s))*(a[m] if m<len(a) else 0)
   assert literal==expansion,(n,m,z,literal,expansion)
   if m==0:assert literal==1+z**n
   checks2+=1
print(json.dumps({'literal_matching_cases':checks2,'status':'PASS','is_general_proof':False}))
