import json,time,sys,itertools,functools,math
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def loopy():
 for n in range(3,12):
  E=[(i,(i+1)%n) for i in range(n)]+[(i,i) for i in range(n)]
  inc=[sum(1<<e for e,(u,v) in enumerate(E) if i in (u,v)) for i in range(n)]
  @functools.lru_cache(None)
  def val(mask):
   if not mask:return 0
   best=-n
   for e in range(2*n):
    if mask>>e&1:
     nxt=mask^(1<<e); gain=sum(1 for v in set(E[e]) if not nxt&inc[v])
     best=max(best,gain+val(nxt) if gain else -val(nxt))
   return best
  for k in range(1,n+1):
   mask=(1<<(n+k))-1; v=val(mask);expect=1 if k<=2 or k%2==0 else -1
   print(json.dumps(dict(id=364032,n=n,k=k,score_difference=v,agrees=(v>0)-(v<0)==expect,states=val.cache_info().currsize)),flush=True)
def gf():
 def rem(a,b):
  while a.bit_length()>=b.bit_length():a^=b<<(a.bit_length()-b.bit_length())
  return a
 def mul(a,b,p):
  c=0
  while b:
   if b&1:c^=a
   b>>=1;a<<=1
   if a.bit_length()==p.bit_length():a^=p
  return c
 def power(a,k,p):
  r=1
  while k:
   if k&1:r=mul(r,a,p)
   a=mul(a,a,p);k>>=1
  return r
 for n in [2,4,6,8]:
  polys=[p for p in range((1<<n)+1,1<<(n+1),2) if all(rem(p,b) for j in range(1,n//2+1) for b in range((1<<j)+1,1<<(j+1),2))];count=0;bad=[]
  for p in polys:
   inv=[0]+[power(a,(1<<n)-2,p) for a in range(1,1<<n)]
   sq=[mul(a,a,p) for a in range(1<<n)]
   rounds=[]
   for k in range(n):
    rounds.append(inv[:]);inv=[sq[x] for x in inv]
   for b in range(1<<n):
    perm=list(range(1<<n))
    for tab in rounds:perm=[tab[x^b] for x in perm]
    cycles=0;seen=set()
    for a in range(1<<n):
     if a not in seen:
      cycles+=1;x=a
      while x not in seen:seen.add(x);x=perm[x]
    count+=1
    if cycles==1:bad.append([p,b])
  print(json.dumps(dict(id=340354,n=n,irreducibles=len(polys),cases=count,unicyclic=bad)),flush=True)
def prefix():
 from sympy.combinatorics import Permutation,PermutationGroup
 def rev(n,k):return Permutation(list(range(k-1,-1,-1))+list(range(k,n)))
 def group(n,m,k):return PermutationGroup([rev(n,j) for j in [n,m,k]])
 for n in range(4,22):
  if n%4 not in [0,1]:continue
  count=ante=0;bad=[]
  for m in range(3,n):
   for k in range(2,m):
    count+=1
    if group(n,m,k).order()==math.factorial(n):
     ante+=1
     if group(n+2,m+2,k+2).order()!=math.factorial(n+2):bad.append([n,m,k])
  print(json.dumps(dict(id=371616,n=n,cases=count,antecedents=ante,counterexamples=bad,method='exact Schreier Sims order')),flush=True)
if __name__=='__main__':globals()[sys.argv[1]]()
