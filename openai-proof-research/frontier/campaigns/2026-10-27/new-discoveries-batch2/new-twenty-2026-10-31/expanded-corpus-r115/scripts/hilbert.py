import math,json,time
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def parts(n,m=None):
 if n==0: yield ();return
 for j in range(min(n,m or n),1-1,-1):
  for p in parts(n-j,j):yield (j,)+p
def lisdist(n):
 a=[0]*(n+1)
 if n==0:return [1]
 for p in parts(n):
  hook=1
  for i,l in enumerate(p):
   for j in range(l):hook*=l-j+sum(t>j for t in p[i+1:])
  f=math.factorial(n)//hook;a[p[0]]+=f*f
 assert sum(a)==math.factorial(n)
 return a
N=36;R=20;facts=[math.factorial(n) for n in range(N+1)];A=[lisdist(n) for n in range(N+1)]
out=[]
for r in range(1,R+1):
 powers=[[1]]
 for t in range(N):
  old=powers[-1];new=[0]*(len(old)+r-1);s=0
  for j in range(len(new)):
   if j-1>=0 and j-1<len(old):s+=old[j-1]
   if j-r>=0 and j-r<len(old):s-=old[j-r]
   new[j]=s
  powers.append(new)
 for n in range(1,N+1):
  c=[0]*(r*n+1)
  for m in range(n+1):
   factor=math.comb(n,m)**2*facts[n-m]
   for l,a in enumerate(A[m]):
    if a:
     for j,b in enumerate(powers[n-m]):
      if b:c[r*(m-l)+j]+=factor*a*b
  assert sum(c)==facts[n]*r**n
  fallen=False;bad=False
  for x,y in zip(c,c[1:]):
   if x>y:fallen=True
   if x<y and fallen:bad=True
  out.append({'n':n,'r':r,'unimodal':not bad,'peak_degree':max(range(len(c)),key=c.__getitem__)})
  if bad:
   (D/'outputs/hilbert-counterexample.json').write_text(json.dumps({'n':n,'r':r,'coefficients':c}));print('COUNTEREXAMPLE',n,r,flush=True)
 print('completed r',r,flush=True)
(D/'outputs/hilbert.json').write_text(json.dumps(out,indent=2)+'\n')
