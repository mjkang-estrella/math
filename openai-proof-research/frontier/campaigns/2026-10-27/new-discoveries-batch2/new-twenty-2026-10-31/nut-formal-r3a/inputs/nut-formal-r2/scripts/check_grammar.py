from pathlib import Path
import itertools,json
root=Path(__file__).resolve().parents[1]
def det(a):
 a=[r[:] for r in a];n=len(a);s=1;prev=1
 for k in range(n-1):
  p=next((i for i in range(k,n) if a[i][k]),None)
  if p is None:return 0
  if p!=k:a[k],a[p]=a[p],a[k];s=-s
  pivot=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    v=a[i][j]*pivot-a[i][k]*a[k][j];assert v%prev==0;a[i][j]=v//prev
   a[i][k]=0
  prev=pivot
 return s*a[-1][-1]
def minor(a,i):return det([[x for j,x in enumerate(r) if j!=i] for k,r in enumerate(a) if k!=i])
def decode(s):
 bits=[(ord(c)-63)>>j&1 for c in s[1:] for j in range(5,-1,-1)];a=[[0]*8 for _ in range(8)];k=0
 for j in range(1,8):
  for i in range(j):a[i][j]=a[j][i]=bits[k];k+=1
 return a
def augment(a,edges,k,d):
 if k==len(edges):
  b=[r[:] for r in a]
  for i in range(8):b[i][i]=d[i]
  yield b;return
 i,j=edges[k]
 yield from augment(a,edges,k+1,d)
 if d[i] and d[j]:
  a[i][j]=a[j][i]=2;d[i]-=1;d[j]-=1
  yield from augment(a,edges,k+1,d)
  d[i]+=1;d[j]+=1;a[i][j]=a[j][i]=1
counts=dict(underlying=0,augmented=0,signings=0,singular=0,surviving=0);examples=[];certificates=[];unsigned_set=set();signed_set=set()
for line in (root/'inputs/expanded-corpus-r111/sources/graph8.g6').read_text().splitlines():
 a=decode(line);deg=list(map(sum,a))
 if max(deg)>3:continue
 edges=[(i,j) for j in range(8) for i in range(j) if a[i][j]];seen={0};tree=set()
 while True:
  e=next((e for e in edges if (e[0] in seen)!=(e[1] in seen)),None)
  if e is None:break
  tree.add(e);seen.update(e)
 if len(seen)!=8:continue
 counts['underlying']+=1
 for b in augment(a,edges,0,[3-x for x in deg]):
  counts['augmented']+=1;unsigned_set.add(tuple(map(tuple,b)))
  signs=[e for e in edges if e not in tree]+[(i,i) for i in range(8) if b[i][i]]
  for sig in itertools.product([1,-1],repeat=len(signs)):
   c=[r[:] for r in b]
   for (i,j),v in zip(signs,sig):c[i][j]=c[j][i]=v*b[i][j]
   if len({c[i][i] for i in range(8) if b[i][i]==1})>1:continue
   counts['signings']+=1;signed_set.add(tuple(map(tuple,c)))
   value=det(c)
   if value:
    certificates.append(dict(matrix=c,det=value));continue
   counts['singular']+=1
   cof=[minor(c,i) for i in range(8)]
   if 0 in cof:certificates.append(dict(matrix=c,zero_principal_minor=cof.index(0)))
   if all(cof):
    counts['surviving']+=1
    if len(examples)<5:examples.append(dict(matrix=c,cofactors=cof,unsigned=b,unsigned_det=det(b),unsigned_cofactors=[minor(b,i) for i in range(8)]))
counts['distinct_unsigned_matrices']=len(unsigned_set);counts['distinct_signed_matrices']=len(signed_set)
(root/'all-normalized-certificates.json').write_text(json.dumps(certificates)+'\n')
(root/'grammar-check.json').write_text(json.dumps(dict(counts=counts,examples=examples),indent=2)+'\n')
print(json.dumps(dict(counts=counts,examples=examples)))
