import itertools as it, pathlib,json,time
start=time.monotonic()
def cyclic(n):return [[(a+b)%n for b in range(n)] for a in range(n)]
def product(ns):
 vs=list(it.product(*(range(n) for n in ns)));idx={v:i for i,v in enumerate(vs)}
 return [[idx[tuple((a+b)%n for a,b,n in zip(x,y,ns))] for y in vs] for x in vs]
def dihedral(m):return [[((a%m+(-1 if a//m else 1)*(b%m))%m)+m*((a//m+b//m)%2) for b in range(2*m)] for a in range(2*m)]
def trans(A,B,t):
 def f(left,unused,syms):
  if not left:return True
  opts=[(sum(not(syms>>t[a][b]&1) for b in unused),a) for a in left];_,a=min(opts)
  for b in unused:
   c=t[a][b]
   if not syms>>c&1 and f(left-{a},unused-{b},syms|1<<c):return True
  return False
 return f(set(A),set(B),0)
def isgroup(H,t):return 0 in H and all(t[a][b] in H for a in H for b in H)
def hpbad(H,t):
 k=len(H);p=1
 while k%2==0:p*=2;k//=2
 if p==1:return False
 for a in H:
  b=a;o=1
  while b!=0:b=t[b][a];o+=1
  if o%p==0:return True
 return False
for name,t in [(f'C{n}',cyclic(n)) for n in range(2,11)]+[('C2x2',product([2,2])),('C2^3',product([2,2,2])),('C4x2',product([4,2])),('D6',dihedral(3)),('D8',dihedral(4)),('D10',dihedral(5))]:
 N=len(t);count=non=exc=0;bad=[]
 # normalise both sets to contain the identity; exhaust every such ordered pair
 subs={n:[(0,)+s for s in it.combinations(range(1,N),n-1)] for n in range(1,N+1)}
 for n,sets in subs.items():
  for A in sets:
   for B in sets:
    count+=1
    if trans(A,B,t):continue
    non+=1;As=set(A);Bs=set(B)
    if As==Bs and isgroup(As,t) and hpbad(As,t):exc+=1;continue
    # normalized exceptional sets of size 2^k-2: allow every subgroup and translation
    okay=False
    if n+2<=N and (n+2)&(n+1)==0:
     for Ht in it.combinations(range(N),n+2):
      H=set(Ht)
      if not isgroup(H,t) or not all(t[a][a]==0 for a in H):continue
      for g in range(N):
       AA={t[g][a] for a in A}
       if not AA<=H:continue
       for h in range(N):
        BB={t[h][b] for b in B}
        if BB<=H:
         missing=list(H-AA)+list(H-BB);v=0
         for x in missing:v=t[v][x]
         if v==0:okay=True;break
       if okay:break
      if okay:break
    if okay:exc+=1
    else:bad.append([A,B])
 print(json.dumps(dict(group=name,order=N,normalized_pairs=count,no_transversal=non,source_exceptions=exc,unclassified=bad,seconds=time.monotonic()-start)),flush=True)
