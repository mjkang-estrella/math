# Copyright (c) 2026 Myeongjin Kang. MIT License.
from fractions import Fraction as Q

def edgeset(es): return sorted({tuple(sorted(e)) for e in es})
def prism(m): return 2*m,edgeset([(i,(i+1)%m) for i in range(m)]+[(m+i,m+(i+1)%m) for i in range(m)]+[(i,m+i) for i in range(m)])
def pm(n,es):
 adj=[[] for _ in range(n)]
 for i,(u,v) in enumerate(es): adj[u].append((v,i));adj[v].append((u,i))
 def f(mask,chosen):
  if not mask: yield tuple(chosen);return
  u=(mask&-mask).bit_length()-1
  for v,i in adj[u]:
   if mask>>v&1: yield from f(mask^(1<<u)^(1<<v),chosen+[i])
 return f((1<<n)-1,[])
def hcs(n,es):
 ans=[]
 for mat in pm(n,es):
  c=[1]*len(es)
  for i in mat:c[i]=0
  adj=[[] for _ in range(n)]
  for i,(u,v) in enumerate(es):
   if c[i]:adj[u].append(v);adj[v].append(u)
  seen={0};stack=[0]
  while stack:
   for v in adj[stack.pop()]:
    if v not in seen:seen.add(v);stack.append(v)
  if len(seen)==n:ans.append(c)
 return ans

def rank(a):
 if not a:return 0
 a=[[Q(x) for x in r] for r in a];r=0
 for j in range(len(a[0])):
  k=next((k for k in range(r,len(a)) if a[k][j]),None)
  if k is None:continue
  a[r],a[k]=a[k],a[r];q=a[r][j];a[r]=[x/q for x in a[r]]
  for k in range(r+1,len(a)):
   q=a[k][j]
   if q:a[k]=[x-q*y for x,y in zip(a[k],a[r])]
  r+=1
  if r==len(a):break
 return r

def join(g,h,u=0,v=0,perm=(0,1,2)):
 n,e=g;m,f=h;un=[b if a==u else a for a,b in e if u in (a,b)];vn=[b if a==v else a for a,b in f if v in (a,b)]
 left={a:i for i,a in enumerate(a for a in range(n) if a!=u)};right={a:n-1+i for i,a in enumerate(a for a in range(m) if a!=v)}
 es=[(left[a],left[b]) for a,b in e if u not in (a,b)]+[(right[a],right[b]) for a,b in f if v not in (a,b)]+[(left[a],right[vn[perm[i]]]) for i,a in enumerate(un)]
 return n+m-2,edgeset(es)

def square_expand(g,i,j):
 n,e=g;u,v=e[i];w,z=e[j]
 if len({u,v,w,z})<4:return None
 es=[x for k,x in enumerate(e) if k not in (i,j)]+[(n,n+1),(n+1,n+2),(n+2,n+3),(n+3,n),(u,n),(v,n+3),(w,n+1),(z,n+2)]
 return n+4,edgeset(es)
if __name__=='__main__':
 for m in range(4,22,2):
  n,e=prism(m);c=hcs(n,e);r=rank([[x-y for x,y in zip(a,c[0])] for a in c[1:]])
  print('prism',m,'HC',len(c),'affine rank',r,'target',n//2+1,flush=True)
 for m in range(4,12,2):
  n,e=join(prism(m),prism(4));c=hcs(n,e);r=rank([[x-y for x,y in zip(a,c[0])] for a in c[1:]])
  print('splice',m,4,'HC',len(c),'affine rank',r,'target',n//2+1,flush=True)
