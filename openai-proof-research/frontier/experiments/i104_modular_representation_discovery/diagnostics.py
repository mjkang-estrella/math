"""Exact finite diagnostics; independent of the universal proofs in the report.
No writes, network calls, or bytecode creation when run with python -B.
"""
from itertools import permutations
from math import gcd
import json

def group(degree,even=False):
 ps=[a for a in permutations(range(degree)) if not even or sum(a[i]>a[j] for i in range(degree) for j in range(i+1,degree))%2==0]
 pos={a:i for i,a in enumerate(ps)}
 mul=[[pos[tuple(a[b[i]] for i in range(degree))] for b in ps] for a in ps]
 inv=[next(j for j in range(len(ps)) if mul[i][j]==0) for i in range(len(ps))]
 orders=[]
 for i in range(len(ps)):
  v=i;o=1
  while v: v=mul[v][i];o+=1
  orders.append(o)
 return mul,inv,orders

def subgroups(mul):
 def close(h,g):
  gens=list(h)+[g];s={0};todo=[0]
  while todo:
   x=todo.pop()
   for a in gens:
    y=mul[x][a]
    if y not in s:s.add(y);todo.append(y)
  return frozenset(s)
 seen={frozenset([0])};todo=list(seen)
 while todo:
  h=todo.pop()
  for g in range(len(mul)):
   if g not in h:
    k=close(h,g)
    if k not in seen:seen.add(k);todo.append(k)
 return sorted(seen,key=lambda h:(len(h),sorted(h)))

def twisted_counts(degree,even,p,t,max_s=10,h=8):
 mul,inv,orders=group(degree,even);N=len(mul);hs=subgroups(mul)
 modulus=N*p**h
 def power(g,a):
  z=0
  for _ in range(a%orders[g]):z=mul[z][g]
  return z
 data=[]
 for H in hs:
  li=sorted(H);pos={x:i for i,x in enumerate(li)};tab=[[pos[mul[x][y]] for y in li] for x in li]
  w=[int(orders[x]%p==0) for x in li]
  handle=[0]*len(li)
  for x in li:
   for y in li:
    c=mul[mul[mul[x][y]][inv[x]]][inv[power(y,t)]]
    handle[pos[c]]+=1
  def conv(a,b):
   z=[0]*len(li)
   for i,ai in enumerate(a):
    if ai:
     for j,bj in enumerate(b):
      if bj:z[tab[i][j]]=(z[tab[i][j]]+ai*bj)%modulus
   return z
  def times(a,b):
   z=[1]+[0]*(len(a)-1)
   while b:
    if b&1:z=conv(z,a)
    a=conv(a,a);b//=2
   return z
  counts=[]
  for s in range(max_s+1):
   a=times(w,p**s)
   counts.append(sum(a[i]*handle[i] for i in range(len(li)))%modulus)
  data.append(counts)
 for i,H in enumerate(hs):
  for j,K in enumerate(hs[:i]):
   if K<H:data[i]=[(a-b)%modulus for a,b in zip(data[i],data[j])]
 Z=sum(all(mul[x][y]==mul[y][x] for y in range(N)) for x in range(N))
 orbit=N//Z
 assert all(n%orbit==0 for n in data[-1])
 return {'group':('A' if even else 'S')+str(degree),'p':p,'t':t,'subgroups':len(hs),'modulus':p**h,'s_range':[0,max_s],'generating_orbit_residues':[n//orbit for n in data[-1]]}

def mu(n):
 out=1;d=2
 while d*d<=n:
  if n%d==0:
   n//=d;out=-out
   if n%d==0:return 0
  else:d+=1
 if n>1:out=-out
 return out

def phi(n):return sum(gcd(i,n)==1 for i in range(1,n+1))

def reconstruction():
 checks=0
 def parts(n,minimum=1):
  if n==0:yield []
  for i in range(minimum,n+1):
   for rest in parts(n-i,i):yield [i]+rest
 for L in range(1,16):
  for ls in parts(L):
   K={d:sum(gcd(d,m) for m in ls) for d in range(1,L+1)}
   a={d:sum(mu(d//e)*K[e] for e in range(1,d+1) if d%e==0)//phi(d) for d in range(1,L+1)}
   c={m:sum(mu(j)*a[m*j] for j in range(1,L//m+1)) for m in range(1,L+1)}
   assert all(c[m]==ls.count(m) for m in c)
   checks+=1
 return checks

def main():
 out={'status':'finite evidence only','cycle_reconstructions':reconstruction(),'twisted':[]}
 for args in [(3,False,2,5),(5,True,2,7),(5,True,2,17),(5,True,3,13),(5,True,5,11)]:
  out['twisted'].append(twisted_counts(*args))
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
