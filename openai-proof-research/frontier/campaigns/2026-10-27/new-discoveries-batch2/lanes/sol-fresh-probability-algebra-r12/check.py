#!/usr/bin/env python3
"""Exact diagnostics, not a classification or novelty certificate."""
import os
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS']: os.environ[key]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(20,20))
import json
from pathlib import Path

def bil(u,v,m):
    mask=(1<<m)-1
    return ((u&mask)&(v>>m)).bit_count()%2

def form(u,v,m):return bil(u,v,m)^bil(v,u,m)

def ring_product(x,y,m,unital=False):
    n=1<<(2*m)
    if not unital:return n*bil(x%n,y%n,m)
    # encoding u + n*c + 2*n*a; (a,u,c)(b,v,d)=(ab,av+bu,ad+bc+B(u,v))
    u,c,a=x%n,(x//n)%2,x//(2*n)
    v,d,b=y%n,(y//n)%2,y//(2*n)
    return (a*v^b*u)+n*(a*d^b*c^bil(u,v,m))+2*n*(a*b)

out={}
# Exhaustive associativity/additive distributivity for the unital m=2 ring (64 elements).
m=2;N=1<<(2*m+2)
table=[[ring_product(x,y,m,True) for y in range(N)] for x in range(N)]
for x in range(N):
 for y in range(N):
  for z in range(N):
   assert table[table[x][y]][z]==table[x][table[y][z]]
   assert table[x][y^z]==table[x][y]^table[x][z]
   assert table[x^y][z]==table[x][z]^table[y][z]
out['unital_m2_exhaustive_triples']=N**3
rows=[]
for m in [2,3,4]:
 a=1<<m;v=a*a-1;k=a*a//2-2;lam=a*a//4-3;mu=a*a//4-1
 adj=[sum(1<<j for j,w in enumerate(range(1,v+1)) if u!=w and form(u,w,m)==0) for u in range(1,v+1)]
 assert all(x.bit_count()==k for x in adj)
 for i in range(v):
  for j in range(v):
   target=k if i==j else (lam if adj[i]>>j&1 else mu)
   assert (adj[i]&adj[j]).bit_count()==target
 # The exact A^2 identity plus symmetry yields the two nonprincipal roots.
 r=a//2-1;s=-a//2-1;f=(a*a+a-2)//2;g=(a*a-a-2)//2
 assert f+g+1==v and k+f*r+g*s==0
 assert r*r+2*r==a*a//4-1 and s*s+2*s==a*a//4-1
 for t in [2,4]:
  n=t*v;d=t*(k+1)-1;delta=(n-1)*d
  spec=[(d,1),(t*(r+1)-1,f),(t*(s+1)-1,g),(-1,v*(t-1))]
  assert sum(mult for eig,mult in spec)==n
  assert sum(eig*mult for eig,mult in spec)==0
  assert sum(eig*eig*mult for eig,mult in spec)==n*d
  energy=sum(abs(eig)*mult for eig,mult in spec)
  if m<=3:
   verts=[(u,c) for u in range(1,v+1) for c in range(t)]
   full=[sum(1<<j for j,(w,b) in enumerate(verts) if i!=j and form(u,w,m)==0) for i,(u,c) in enumerate(verts)]
   for i in range(n):
    second=0
    for j in range(n):
     if full[i]>>j&1:second|=full[j]
    second&=~(1<<i)
    assert second==((1<<n)-1)^(1<<i)
    assert full[i].bit_count()==d
  rows.append(dict(m=m,fiber=t,ring_order=t*a*a,vertices=n,degree=d,delta2=delta,spectrum=spec,ordinary_energy=energy,msn_energy=delta*energy,complete_msn_energy=2*(n-1)**3,hyper=delta*energy>2*(n-1)**3))
# Direct exact ring/graph correspondence for full unital m=3 ring.
m=3;N=1<<(2*m+2);center=[]
for x in range(N):
 if all(ring_product(x,y,m,True)==ring_product(y,x,m,True) for y in range(N)):center.append(x)
assert len(center)==4
out.update(rows=rows,unital_m3_center=center,status='PASS',credit=0)
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
