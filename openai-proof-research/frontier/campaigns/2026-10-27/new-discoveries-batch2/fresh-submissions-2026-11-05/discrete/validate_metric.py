import json,random
from pathlib import Path
from check_metric import regular,sig,iso
rng=random.Random(15)
def rank(cols):
 piv={}
 for v in cols:
  while v:
   p=v.bit_length()-1
   if p not in piv:piv[p]=v;break
   v^=piv[p]
 return len(piv)
def direct(a,S):
 n=len(a);vs=[[],[],[]];cs=[[],[],[]]
 for i in range(n):vs[0 if S>>i&1 else 1].append(i)
 for i in range(n):
  for j in range(i+1,n):
   if a[i]>>j&1:
    w=2-(S>>i&1)-(S>>j&1);cs[w].append((i,j))
 ans=[]
 for w in range(3):
  columns=[]
  for i,j in cs[w]:
   col=0
   if i in vs[w]:col|=1<<i
   if j in vs[w]:col|=1<<j
   columns.append(col)
  r=rank(columns);ans.append((len(vs[w])-r,len(cs[w])-r))
 return (ans[0][0],ans[0][1],ans[1][0],ans[1][1],ans[2][1])
def formula(a,S):
 n=len(a);W=((1<<n)-1)^S;k=S.bit_count();e=sum((a[i]&S).bit_count() for i in range(n) if S>>i&1)//2
 cross=sum((a[i]&W).bit_count() for i in range(n) if S>>i&1);z=sum(not a[i]&S for i in range(n) if W>>i&1)
 todo=S;c=0
 while todo:
  c+=1;fr=todo&-todo
  while fr:
   todo&=~fr;ne=0
   for i in range(n):
    if fr>>i&1:ne|=a[i]
   fr=ne&todo
 return c,e-k+c,z,cross-(n-k)+z,sum(x.bit_count() for x in a)//2-e-cross
checks=0
for n in range(2,11):
 for _ in range(20):
  a=[0]*n
  for i in range(n):
   for j in range(i+1,n):
    if rng.randrange(2):a[i]|=1<<j;a[j]|=1<<i
  for _ in range(20):
   S=rng.randrange(1<<n);assert direct(a,S)==formula(a,S);checks+=1
# negative isomorphism control: prism vs K3,3
A=[(1<<((i+1)%3))|(1<<((i+2)%3))|(1<<(i+3)) for i in range(3)]
A += [(1<<(3+(i+1)%3))|(1<<(3+(i+2)%3))|(1<<i) for i in range(3)]
B=[56]*3+[7]*3
assert not iso(A,B)
assert sig(A)!=sig(B)
out={'matrix_checks':checks,'field':'F_2','assertions_passed':True,'isomorphism_control':'triangular prism not isomorphic to K3,3; metric distinguishes','scope':'Validation of evaluator, not universal theorem.'}
Path(__file__).with_name('metric-validation.json').write_text(json.dumps(out,indent=2));print(out)
