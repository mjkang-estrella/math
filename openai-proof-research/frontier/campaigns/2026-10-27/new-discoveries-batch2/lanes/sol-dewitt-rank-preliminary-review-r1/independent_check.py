from pathlib import Path
from math import isqrt
from functools import cache
from collections import Counter
import json
@cache
def divisors(n):
 return tuple(sorted({x for d in range(1,isqrt(n)+1) if n%d==0 for x in (d,n//d)}))
def parts(n):
 # Enumerate rectangle areas first, then independently factor each area.
 return {(a,k//a,b,(n-k)//b) for k in range(1,n) for a in divisors(k) for b in divisors(n-k) if a>b}
def C(p):
 a,c,b,d=p;return c+d,b,c,a-b
def T(p):
 a,c,b,d=p
 def pair(a,c):
  aa=a&-a;cc=c&-c;return (a//aa*cc,c//cc*aa)
 pairs=sorted([pair(a,c),pair(b,d)],reverse=True)
 assert pairs[0][0]!=pairs[1][0]
 return sum(pairs,())
def R(p):
 a,c,b,d=p;z=sorted([(c,a),(d,b)],reverse=True);assert c!=d;return sum(z,())
def S(p):
 a,c,b,d=p;return a%4==2 and c%2 and b%2 and d%4==0 and a!=2*b
P=[(16,14),(36,30),(72,42),(196,70),(252,114)]
ns=sorted(set(range(2,303,4))|{A*n+B for A,B in P for n in range(5)})
ct=Counter();rows=[]
for n in ns:
 ps=parts(n);cl=Counter(''.join('O' if v%2 else 'E' for v in p) for p in ps)
 X={p for p in ps if p[0]%2 and p[1]%2==0 and p[2]%2 and p[3]%2==0}
 Z={p for p in ps if p[0]%2==0 and p[1]%2 and p[2]%2==0 and p[3]%2}
 Y={p for p in ps if p[0]%2 and p[1]%2==0 and p[2]%2==0 and p[3]%2}
 ss={p for p in ps if S(p)};im=set()
 for p in ps:
  assert C(p) in ps and C(C(p))==p;ct['conjugations']+=1
 for p in X:
  q=T(p);assert q in Z and T(q)==p;im.add(q);ct['valuation_maps']+=1
 assert len(im)==len(X)
 def odd(a):return a//(a&-a)
 assert Z-im=={p for p in Z if odd(p[0])==odd(p[2])}
 phi=[]
 for a,c,b,d in X:
  if c%4==2:q=(2*a,c//2,b,d)
  else:
   assert d%4==2
   q=(2*b,d//2,a,c) if 2*b>a else (a,c,2*b,d//2)
  phi.append(q)
 y1={p for p in Y if p[2]%4==2}
 assert len(phi)==len(set(phi)) and set(phi)==ss|y1
 assert {C(p) for p in y1}==Y-y1
 fixed=[]
 for p in ss:
  w=C(p);u,x,v,y=w
  assert u>v and all(t%2 for t in w) and u%4==v%4 and x%4==y%4 and x!=y
  z=R(w);q=C(z);assert q in ss and C(R(C(q)))==p
  assert (z==w)==((u==x and v==y) or (u==y and v==x))
  if z==w:fixed.append(w)
  ct['S_maps']+=1
 es=sum((a+b-d)%2==0 for a,c,b,d in ps);er=sum((a-c-d)%2==0 for a,c,b,d in ps)
 m=n//2;ds=divisors(m)
 assert es==2*len(X)+len(Y) and er==2*len(Z)+len(Y)
 assert er-es==sum(ds)-len(ds) and (es-2*len(ss))%4==0
 nonsq=not any(isqrt(n-i*i)**2==n-i*i for i in range(isqrt(n)+1))
 if nonsq:
  assert len(fixed)==(len(ds)//2 if m%4==1 else 0)
  assert es%4==(len(ds)%4 if m%4==1 else 0);ct['nonsquare_formula']+=1
 for A,B in P:
  if n>=B and (n-B)%A==0:
   assert es%4==0 and (len(ps)-es)%4==0
   if A!=16:assert er%4==0 and (len(ps)-er)%4==0
   rows.append([A,B,n,er,es,len(ps)]);ct['progression_rows']+=1
 ct['N_cases']+=1
print(json.dumps({'status':'PASS','method':'rectangle-area factorization; explicit valuation and phi image set equality; conjugation and reversal fixed point classification','counts':ct,'max_N':max(ns),'progressions':rows},indent=2))
