import json,math,itertools,hashlib
F=[0,1]
for _ in range(30):F.append(sum(F[-2:]))
def quotient(A,B):
 d=sum(A)-sum(B);p=[0]*(d+1);p[0]=1
 for a in A:
  for k in range(d,a-1,-1):p[k]-=p[k-a]
 for b in B:
  for k in range(b,d+1):p[k]+=p[k-b]
 return p
def direct(A,B):
 p=[1]
 for a in A:
  t=[0]*(len(p)+a-1)
  for i,v in enumerate(p):
   for j in range(a):t[i+j]+=v
  p=t
 for b in B:
  # divide by [b] using its monic leading coefficient
  t=p[:];q=[0]*(len(t)-b+1)
  for k in range(len(q)-1,-1,-1):
   q[k]=t[k+b-1]
   for j in range(b):t[k+j]-=q[k]
  assert not any(t)
  p=q
 return p
def good(p):return all(p[k]>=p[k-1] for k in range(1,len(p)//2+len(p)%2))
def match(m,n):
 edges={j:[i for i in range(m+1,m+n+1) if F[i]%F[j]==0] for j in range(3,n+1)};used={}
 def visit(j,seen):
  for i in edges[j]:
   if i in seen:continue
   seen.add(i)
   if i not in used or visit(used[i],seen):used[i]=j;return True
  return False
 return all(visit(j,set()) for j in edges),edges
rows=[];ind=0;ident=0
for n in range(1,13):
 for m in range(n,25-n):
  A=F[m+1:m+n+1];B=F[1:n+1];p=quotient(A,B)
  assert min(p)>=0 and p==p[::-1] and good(p)
  # exact factor-at-q=1 check
  assert sum(p)*math.prod(B)==math.prod(A)
  rows.append({'m':m,'n':n,'degree':len(p)-1,'peak':max(p),'sha256':hashlib.sha256(','.join(map(str,p)).encode()).hexdigest()})
  if m+n<=12:
   assert direct(A,B)==p;ind+=1
  # full exact cleared first-difference identity, independently by denominator coin counts
  if m+n<=16:
   d=len(p)-1;P=[0]*(d+1);P[0]=1
   for b in B[1:]:
    for k in range(b,d+1):P[k]+=P[k-b]
   z=P[:]
   for a in A:
    for k in range(d,a-1,-1):z[k]-=z[k-a]
   assert z==[p[0]]+[p[k]-p[k-1] for k in range(1,d+1)];ident+=1
print(json.dumps({'rows':rows,'independent_long_divisions':ind,'difference_identities':ident,'matching_6_6':match(6,6)},indent=2))
# Find a genuine obstruction to inferring unimodality from positive polynomiality,
# fixed Fibonacci denominator, and all relation degrees >= F[n+1].
found=None
for n in [4,5,6]:
 for A in itertools.combinations_with_replacement(range(F[n+1],F[n+1]+16),n):
  p=quotient(A,F[1:n+1])
  # quotient() computes only through predicted degree; verify exact product identity separately
  if p!=p[::-1] or min(p)<0 or good(p):continue
  # polynomial divisibility iff every cyclotomic exponent nonnegative
  if any(sum(a%r==0 for a in A)<sum(b%r==0 for b in F[1:n+1]) for r in range(2,max(A)+1)):continue
  found={'n':n,'A':A,'B':F[1:n+1],'p':p};break
 if found:break
print('GENERIC_OBSTRUCTION',json.dumps(found))
