exec(open(__file__.replace('flag-betti.py','flag-search.py')).read().split('for n in [2,3,4]:')[0])
from itertools import product
from functools import lru_cache

def rank(rows,p=1000003):
 if not rows:return 0
 a=[row[:] for row in rows];r=0
 for c in range(len(a[0])):
  pivot=next((i for i in range(r,len(a)) if a[i][c]%p),None)
  if pivot is None:continue
  a[r],a[pivot]=a[pivot],a[r];inv=pow(a[r][c]%p,-1,p);a[r]=[x*inv%p for x in a[r]]
  for i in range(r+1,len(a)):
   q=a[i][c]%p
   if q:a[i]=[(x-q*y)%p for x,y in zip(a[i],a[r])]
  r+=1
  if r==len(a):break
 return r

def beta(D,n):
 out={}
 for alpha in product(range(3),repeat=n):
  deg=sum(alpha); bases=[]
  for p in range(n+1):
   bases.append([s for s in range(1<<n) if s.bit_count()==p and all(alpha[i]-((s>>i)&1) in (0,1) for i in range(n)) and sum((alpha[i]-((s>>i)&1))<<i for i in range(n)) in D])
  ranks=[0]
  for p in range(1,n+1):
   mat=[[0]*len(bases[p]) for _ in bases[p-1]]; idx={s:i for i,s in enumerate(bases[p-1])}
   for c,s in enumerate(bases[p]):
    q=0
    for i in range(n):
     if s>>i&1:
      if (s^(1<<i)) in idx:mat[idx[s^(1<<i)]][c]=(-1)**q
      q+=1
   ranks.append(rank(mat))
  ranks.append(0)
  for p in range(n+1):
   v=len(bases[p])-ranks[p]-ranks[p+1]
   if v:out[p,deg]=out.get((p,deg),0)+v
 return out
if __name__=='__main__':
 for n in [3,4]:
  sets=downsets(n);cache={};checked=0;found=None
  for A in sets:
   for B in sets:
    if not B<=A:continue
    D=frozenset(A-B);L=frozenset(lexcomp(A,n)-lexcomp(B,n))
    for W in (D,L):
     if W not in cache:cache[W]=beta(W,n)
    a,b=cache[D],cache[L];checked+=1
    if any(v>b.get(k,0) for k,v in a.items()):
     found=dict(A=names(A,n),B=names(B,n),D=names(D,n),L=names(L,n),beta={str(k):v for k,v in a.items()},lex_beta={str(k):v for k,v in b.items()});break
   if found:break
  print(n,'checked',checked,'D',len(cache),'found',json.dumps(found),flush=True)
  (R/f'packet/private/flag-betti-n{n}.json').write_text(json.dumps(dict(n=n,checked=checked,distinct_D=len(cache),field=1000003,found=found),indent=2))
