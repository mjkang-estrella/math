from pathlib import Path
import itertools,random,json
L=Path(__file__).resolve().parents[1]
def spaces(n):
 S={frozenset([0])};todo=list(S)
 while todo:
  a=todo.pop()
  for v in range(1,1<<n):
   if v in a:continue
   b=a|frozenset(x^v for x in a)
   if b not in S:S.add(b);todo.append(b)
 return sorted(S,key=lambda x:(len(x),tuple(sorted(x))))
def mul(a,b,p):
 c=0
 while b:
  if b&1:c^=a
  b>>=1;a<<=1
  if a.bit_length()==p.bit_length():a^=p
 return c
def rank(vec,p):
 B={}
 q=1<<(p.bit_length()-1)
 for a in vec:
  a=list(a)
  for i in range(len(a)):
   if not a[i]:continue
   if i in B:
    z=a[i];a=[x^mul(z,y,p) for x,y in zip(a,B[i])]
   else:
    inv=next(j for j in range(1,q) if mul(a[i],j,p)==1)
    B[i]=[mul(x,inv,p) for x in a];break
 return len(B)
def failure(S,r,n):
 cir=[a for a in S if r[a] < len(a).bit_length()-1 and all(r[b]==len(b).bit_length()-1 for b in S if b<a)]
 rel=[1<<i for i in range((1<<n)-1)]
 for a in cir:
  mask=sum(1<<(v-1) for v in a if v)
  for v in a:
   if v:rel[v-1]|=mask
 for x in range(len(rel)):
  for y in range(len(rel)):
   if rel[x]>>y&1 and rel[y]&~rel[x]:
    z=(rel[y]&~rel[x]).bit_length()-1;return [x+1,y+1,z+1], [sorted(c) for c in cir]
 return None
rng=random.Random(237)
for n,k,p,count in [(4,2,7,256),(4,2,11,4096),(5,2,11,1000),(5,3,11,1000)]:
 S=spaces(n);orth={a:next(b for b in S if all((x&y).bit_count()%2==0 for x in a for y in b) and len(b)*len(a)==1<<n) for a in S}
 q=1<<(p.bit_length()-1);hits=0
 As=itertools.product(range(q),repeat=k*(n-k)) if n==4 else (tuple(rng.randrange(q) for _ in range(k*(n-k))) for _ in range(count))
 for t,A in enumerate(As):
  G=[[int(i==j) if j<k else A[i*(n-k)+j-k] for j in range(n)] for i in range(k)]
  im={v:tuple(__import__('functools').reduce(int.__xor__,(G[i][j] for j in range(n) if v>>j&1),0) for i in range(k)) for v in range(1<<n)}
  r={a:rank([im[v] for v in a],p) for a in S}
  rd={a:len(a).bit_length()-1-k+r[orth[a]] for a in S}
  if any(r[a]==0 or rd[a]==0 for a in S if len(a)==2):continue
  f=failure(S,r,n)
  if f:
   rd={a:len(a).bit_length()-1-k+r[orth[a]] for a in S};fd=failure(S,rd,n)
   if fd:
    hits+=1;out={'n':n,'k':k,'modulus':p,'G':G,'witness':f,'dual_witness':fd,'ranks':[{'space':sorted(a),'rank':r[a]} for a in S]};(L/'outputs/q-nondegenerate-candidate.json').write_text(json.dumps(out,indent=2));print('FOUND',n,k,p,G,f[0],fd[0],flush=True);raise SystemExit
 print('complete',n,k,p,t+1,'both failures',hits,flush=True)
