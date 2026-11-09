import json,random,math,sys,time
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def emit(name,o):
 (D/f'outputs/{name}.json').write_text(json.dumps(o,indent=2)+'\n');print(name,o,flush=True)
if sys.argv[1]=='bezout':
 def euclid(a,b):
  x,y,z,w=1,0,0,1
  while b:q,a,b=a//b,b,a%b;x,z=z,x-q*z;y,w=w,y-q*w
  return x,y
 def children(t):
  m,n,u,v=t
  return [(2*m+n,m,v,u-2*v),(m+2*n,n,u,v-2*u),(2*m-n,m,-v,u+2*v)]
 random.seed(103);rows=[]
 for root in [2,3]:
  count=bad=0;examples=[]
  # Exhaustive layers 0..11 plus 20000 seeded paths of length 100, each continuing beyond source depth 13.
  layer=[(root,1,0,1)]
  for depth in range(12):
   for m,n,u,v in layer:
    b=(u,v)!=euclid(m,n);bad+=b;count+=1
    if b and len(examples)<3:examples.append([m,n,u,v,*euclid(m,n)])
   layer=[c for t in layer for c in children(t)] if depth<11 else []
  randbad=correctedbad=0
  for k in range(20000):
   t=(root,1,0,1);tc=t
   for depth in range(1,101):
    j=random.randrange(3);t=children(t)[j];tc=children(tc)[j]
    if root==2 and depth==1 and j==2:tc=(tc[0],tc[1],1,-1)
    if depth>=14:
     randbad+=(t[2:]!=euclid(*t[:2]));correctedbad+=(tc[2:]!=euclid(*tc[:2]))
  rows.append(dict(root=root,exhaustive_depths=[0,11],nodes=count,mismatches=bad,examples=examples,random_seed=103,paths=20000,path_depth=100,comparisons_beyond_source=20000*87,random_mismatches=randbad,corrected_mismatches=correctedbad))
 emit('bezout',{'rows':rows,'algorithm_limit':'Euclidean floor-division coefficient convention; Matlab equivalence not certified'})
if sys.argv[1]=='qseries':
 N=int(sys.argv[2]);rows=[]
 for name,rs,ts,signs in [('g2',[1,4],[4,6],{0:1,1:-1,2:1,4:-1}),('h2',[2,3],[2,8],{0:1,2:-1,3:-1})]:
  a=[0]*(N+1);a[0]=1
  for k in range(1,N+1):
   mult=(2 if k%5 in rs else 0)+(1 if k%10 in ts else 0)
   for _ in range(mult):
    for j in range(N,k-1,-1):a[j]-=a[j-k]
  bad=[[n,a[n]] for n in range(N+1) if n%5 in signs and a[n]*signs[n%5]<=0]
  (D/f'outputs/{name}-coefficients.json').write_text(json.dumps(a)+'\n')
  rows.append(dict(name=name,degree=N,tested=sum(n%5 in signs for n in range(N+1)),violations=bad[:100]))
 emit('qseries',{'rows':rows,'h3':'undefined in source (5.13); not substituted','source_verified_cutoff':'not specified'})
