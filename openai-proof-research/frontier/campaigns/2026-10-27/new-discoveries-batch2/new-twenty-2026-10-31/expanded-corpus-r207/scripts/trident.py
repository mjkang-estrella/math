import itertools,json,time,math,sys,random
from pathlib import Path
L=Path(__file__).resolve().parents[1]
def mul(a,b):return tuple(a[b[i]] for i in range(len(a)))
def inv(a):
 b=list(a)
 for i,j in enumerate(a):b[j]=i
 return tuple(b)
def order(gens,n):
 identity=tuple(range(n));strong=[[] for _ in range(n)]; trans=[{} for _ in range(n)]
 def rebuild():
  for i in range(n):
   gs=[g for j in range(i,n) for g in strong[j]]; T={i:identity};Q=[i]
   for x in Q:
    for g in gs:
     y=g[x]
     if y not in T:T[y]=mul(g,T[x]);Q.append(y)
   trans[i]=T
 def sift(g,start):
  for i in range(start,n):
   if g[i] not in trans[i]:return g,i
   g=mul(inv(trans[i][g[i]]),g)
  return identity,n
 for g in gens:
  rebuild();r,i=sift(g,0)
  if i<n:strong[i].append(r)
 while True:
  rebuild();added=False
  for i in range(n):
   T=trans[i]; gs=[g for j in range(i,n) for g in strong[j]]
   for x,t in list(T.items()):
    for g in gs:
     r,j=sift(mul(inv(T[g[x]]),mul(g,t)),i+1)
     if j<n:strong[j].append(r);added=True;break
    if added:break
   if added:break
  if not added:return math.prod(map(len,trans))
def generators(colors):
 k=len(colors);n=3*k+1;gs=[list(range(n)) for _ in range(3)]
 for arm in range(3):
  for j,c in enumerate(colors):
   a=0 if j==0 else arm*k+j;b=arm*k+j+1;c=(c+arm)%3;gs[c][a]=b;gs[c][b]=a
 return list(map(tuple,gs))
start=time.monotonic();out=[]; random.seed(207)
for k in range(int(sys.argv[1]),int(sys.argv[2])+1):
 seqs=[(0,)] if k==1 else []
 if k>1:
  for bits in itertools.product(range(2),repeat=k-2):
   c=[0,1]
   for b in bits:c.append([x for x in range(3) if x!=c[-1]][b])
   seqs.append(tuple(c))
 counts={};completed=0
 for c in seqs[int(sys.argv[3]) if len(sys.argv)>3 else 0:int(sys.argv[4]) if len(sys.argv)>4 else len(seqs)]:
  o=order(generators(c),3*k+1);counts[str(o)]=counts.get(str(o),0)+1;completed+=1
  if o not in [math.factorial(3*k+1),math.factorial(3*k+1)//2]:print('EXCEPTION',k,c,o,flush=True)
  if time.monotonic()-start>105:break
 row={'k':k,'n':3*k+1,'completed':completed,'total_normalized':len(seqs),'orders':counts};out.append(row);print(json.dumps(row),flush=True)
 if time.monotonic()-start>105:break
(L/f'outputs/trident-{chr(45).join(sys.argv[1:])}.json').write_text(json.dumps(out,indent=2))
