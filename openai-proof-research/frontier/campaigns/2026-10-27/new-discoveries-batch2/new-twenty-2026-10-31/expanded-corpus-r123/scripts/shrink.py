import itertools,random,json,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]; rng=random.Random(123)
def moves(y,x,rule):
 n=len(y);out=[]
 for u,v in itertools.combinations(range(n),2):
  c=y[u]
  if c>0 and c==y[v]==x[u][v]:
   ts=[t for t in range(n) if t not in (u,v)]
   if (rule.startswith('S') and any(y[t]>=c for t in ts)) or (rule.startswith('C') and any(y[t]==c and x[u][t]+x[v][t]==c for t in ts)):
    out.append((u,v))
  elif rule=='S1S2' and x[u][v]>max(y[u],y[v]):out.append((u,v))
 if rule=='C1C2C3':
  for s in itertools.combinations(range(n),3):
   c=y[s[0]]
   if c>0 and all(y[v]==c for v in s) and sum(x[u][v] for u,v in itertools.combinations(s,2))==2*c and any(y[t]==c and sum(x[v][t] for v in s)==c for t in range(n) if t not in s):out.append(s)
 return out
def shrink(y,x,s):
 groups=[(i,) for i in range(len(y)) if i not in s]+[s]
 xx=tuple(tuple(sum(x[u][v] for u in a for v in b) if i!=j else 0 for j,b in enumerate(groups)) for i,a in enumerate(groups))
 yy=tuple(sum(row)//2 for row in xx)
 assert all(sum(row)%2==0 for row in xx)
 return yy,xx
def sig(y,x):
 # Necessary isomorphism invariant, so distinct signatures certify nonisomorphism.
 return (len(y),tuple(sorted((y[u],tuple(sorted(x[u]))) for u in range(len(y)))))
counts={}
for n in range(3,13):
 count=0
 for trial in range(1000):
  # Nonnegative sums of cycles give even degrees; retain the assignment-polytope inequalities.
  x=[[0]*n for _ in range(n)]
  for z in range(rng.randrange(1,n+2)):
   s=rng.sample(range(n),rng.randrange(3,n+1))
   for u,v in zip(s,s[1:]+s[:1]):x[u][v]+=1;x[v][u]+=1
  deg=[sum(r) for r in x]
  if max(deg)>8:continue
  y=tuple(v//2 for v in deg);x=tuple(map(tuple,x))
  if any(x[u][v]>min(y[u],y[v]) for u in range(n) for v in range(n)):continue
  count+=1
  for rule in ['C1C2','C1C2C3','S1','S1S2']:
   terminals=[]
   for rep in range(20):
    yy,xx=y,x
    while (ms:=moves(yy,xx,rule)):
     yy,xx=shrink(yy,xx,rng.choice(ms))
    terminals.append(sig(yy,xx))
   if len(set(terminals))>1:
    o={'n':n,'trial':trial,'rule':rule,'y':y,'x':x,'terminal_signatures':terminals};(D/'outputs/shrink-witness.json').write_text(json.dumps(o,indent=2));print('FOUND',o,flush=True);sys.exit()
 counts[n]=count;print(n,count,flush=True)
print('NO DIFFERENT terminal invariant; not a complete isomorphism check',counts)
