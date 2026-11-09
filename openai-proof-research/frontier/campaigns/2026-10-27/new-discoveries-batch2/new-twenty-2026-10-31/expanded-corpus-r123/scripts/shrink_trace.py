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
o=json.loads((D/'outputs/shrink-witness.json').read_text());keep=[i for i in range(o['n']) if o['y'][i]>0];y=tuple(o['y'][i] for i in keep);x=tuple(tuple(o['x'][i][j] for j in keep) for i in keep)
seen={};term={}
def dfs(y,x,path):
 key=(y,x)
 if key in seen:return
 seen[key]=True
 ms=moves(y,x,'S1S2')
 if not ms:term.setdefault(sig(y,x),(y,x,path));return
 for s in ms:dfs(*shrink(y,x,s),path+[s])
dfs(y,x,[])
print('input',y,x)
for v in term.values():print('terminal',v)
(D/'outputs/shrink-traces.json').write_text(json.dumps({'input':[y,x],'terminals':list(term.values()),'states':len(seen)},indent=2))
