import random,itertools as it,json
from pathlib import Path
D=Path(__file__).resolve().parents[1];rng=random.Random(9404)
def shape(p):
 rows=[]
 for x in p:
  for row in rows:
   for j,y in enumerate(row):
    if y>x:row[j],x=x,y;break
   else:row.append(x);break
  else:rows.append([x])
 return tuple(map(len,rows))
def cycleperm(alpha):
 n=sum(alpha);a=list(range(1,n+1));rng.shuffle(a);p=[0]*n;i=0
 for k in alpha:
  c=a[i:i+k];i+=k
  for u,v in zip(c,c[1:]+c[:1]):p[u-1]=v
 return p
def test(lam,colors):
 heights=[sum(r>j for r in lam)for j in range(lam[0])];cells=[(i,j)for j,h in enumerate(heights)for i in range(h)];q={};t=0
 for j,h in enumerate(heights):
  for i in range(h-1,-1,-1):t+=1;q[i,j]=t
 P={}
 for color in set(colors):
  cc={c for c,k in zip(cells,colors)if k==color};cols=[j for j in range(len(heights))if any(c[1]==j for c in cc)];seq=[];slashes=[]
  for j in cols:
   col=sorted(c for c in cc if c[1]==j)
   if j!=cols[-1] and len(col)>1:slashes.append(col.pop())
   top=True
   while col:seq.append(col.pop(0 if top else -1));top=not top
  seq+=slashes[::-1]
  for dst,src in zip(seq,seq[-1:]+seq[:-1]):P[dst]=q[src]
 return all((i,j+1)not in P or v<P[i,j+1]for(i,j),v in P.items())and all((i+1,j)not in P or v<P[i+1,j]for(i,j),v in P.items())
out=[]
for n in [10,12,14,15,16,18,20]:
 alpha=(n-3,2,1);shapes={shape(cycleperm(alpha))for _ in range(1500)};ok=[];miss=[];attempts=0
 for lam in sorted(shapes):
  found=False
  for pair in it.combinations(range(n),2):
   for single in range(n):
    if single in pair:continue
    colors=[0]*n
    for i in pair:colors[i]=1
    colors[single]=2;attempts+=1
    if test(lam,colors):found=True;break
   if found:break
  (ok if found else miss).append(lam)
 r=dict(n=n,alpha=alpha,sampled_permutations=1500,distinct_attainable_shapes=len(shapes),canonical_coloring_found=len(ok),canonical_failures=miss,colorings_tested=attempts);print(r,flush=True);out.append(r);(D/'outputs/coloring.json').write_text(json.dumps(out,indent=2)+'\n')
