import itertools,json,functools,collections,time
n=4;start=time.time()
def addpartial(out,e,a,b,i,coef):
 if a>b:
  for t in range(a-b):
   z=list(e);z[i]=a-1-t;z[i+1]=b+t;out[tuple(z)]+=coef
 elif a<b:
  for t in range(b-a):
   z=list(e);z[i]=b-1-t;z[i+1]=a+t;out[tuple(z)]-=coef
@functools.lru_cache(None)
def las(alpha):
 if all(alpha[i]>=alpha[i+1] for i in range(n-1)):return {alpha+(0,):1}
 i=next(i for i in range(n-1) if alpha[i]<alpha[i+1]);b=list(alpha);b[i],b[i+1]=b[i+1],b[i];p=las(tuple(b));o=collections.Counter()
 for e,c in p.items():
  addpartial(o,e,e[i]+1,e[i+1],i,c)
  z=list(e);z[-1]+=1
  addpartial(o,tuple(z),e[i]+1,e[i+1]+1,i,c)
 return {e:c for e,c in o.items() if c}
def flagged(shape,flags):
 cells=[(r,c) for r,l in enumerate(shape) for c in range(l)];o=collections.Counter();placed={}
 subsets={f:[tuple(i for i in range(1,f+1) if mask>>(i-1)&1) for mask in range(1,1<<f)] for f in flags}
 def rec(k,e):
  if k==len(cells):o[tuple(e)]+=1;return
  r,c=cells[k]
  for v in subsets[flags[r]]:
   if c and placed[r,c-1][-1]>v[0]:continue
   if r and placed[r-1,c][-1]>=v[0]:continue
   placed[r,c]=v;ee=e.copy();ee[-1]+=len(v)-1
   for x in v:ee[x-1]+=1
   rec(k+1,ee)
 rec(0,[0]*(n+1));return dict(o)
rows=[];bad=[]
for lam in itertools.combinations_with_replacement(range(6),n):
 lam=tuple(reversed(lam))
 if not 1<=sum(lam)<=5:continue
 shape=tuple(x for x in lam if x);r=len(shape)
 polys=[flagged(shape,f) for f in itertools.combinations_with_replacement(range(1,n+1),r)]
 for a in set(itertools.permutations(lam)):
  # minimal permutation carrying the sorted partition to a
  used=set();w=[]
  for x in lam:
   j=next(j for j in range(n) if j not in used and a[j]==x);w.append(j+1);used.add(j)
  avoids=not any(w[i]>w[k]>w[j] for i in range(n) for j in range(i+1,n) for k in range(j+1,n))
  flag=las(a) in polys;rows.append({'lambda':lam,'alpha':a,'w':w,'avoids312':avoids,'flagged':flag})
  if flag!=avoids:bad.append(rows[-1])
print(json.dumps({'variables':n,'boxes_through':5,'tested':len(rows),'mismatches':bad,'seconds':time.time()-start,'rows':rows}))
