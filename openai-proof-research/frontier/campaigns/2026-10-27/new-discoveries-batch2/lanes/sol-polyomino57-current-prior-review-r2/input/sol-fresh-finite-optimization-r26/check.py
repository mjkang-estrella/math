import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,signal,time,itertools,json,pathlib,random
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(170,175));signal.alarm(190)
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic();rng=random.Random(260629)
def canon(P):
 mx=min(x for x,y in P);my=min(y for x,y in P)
 return tuple(sorted((x-mx,y-my) for x,y in P))
def grow(S):
 out=set()
 for P in S:
  Q=set(P)
  for x,y in P:
   for c in [(x-1,y),(x+1,y),(x,y-1),(x,y+1)]:
    if c not in Q:out.add(canon(Q|{c}))
 return out
r=5;D={(x,y) for x in range(-r,r+1) for y in range(-r,r+1) if abs(x)+abs(y)<=r}
inter=sorted((x,y) for x,y in D if x*y and abs(x)+abs(y)<r)
# This restricted construction is only a falsifier search, never an optimality search.
candidates=[frozenset(h) for h in itertools.combinations(inter,4)]
def connected(C):
 seen={next(iter(C))};todo=list(seen)
 while todo:
  x,y=todo.pop()
  for p in [(x-1,y),(x+1,y),(x,y-1),(x,y+1)]:
   if p in C and p not in seen:seen.add(p);todo.append(p)
 return seen==C
candidates=[H for H in candidates if connected(D-H)]
initial=len(candidates)
def placements(P):
 w=max(x for x,y in P);h=max(y for x,y in P)
 return [frozenset((x+dx,y+dy) for x,y in P) for dx in range(-r,r-w+1) for dy in range(-r,r-h+1) if all((x+dx,y+dy) in D for x,y in P)]
# Screen candidates against deterministic long, thin 11-cell animals first.
witnesses=[]
for a in range(1,10):
 for b in range(11-a):
  P=canon({(i,0) for i in range(a+1)}|{(0,j) for j in range(1,b+1)}|{(a,-j) for j in range(1,11-a-b)})
  if len(P)==11:witnesses.append(P)
for P in witnesses:
 V=placements(P)
 candidates=[H for H in candidates if any(H.isdisjoint(v) for v in V)]
print('initial',initial,'after thin screen',len(candidates),flush=True)
S={((0,0),)};counts=[]
for n in range(1,12):
 if n>1:S=grow(S)
 counts.append(len(S));print(n,len(S),round(time.monotonic()-start,3),flush=True)
 if n==11:
  ordered=sorted(S);rng.shuffle(ordered)
  tested=0;last=[]
  for P in ordered:
   V=placements(P)
   old=len(candidates)
   candidates=[H for H in candidates if any(H.isdisjoint(v) for v in V)]
   tested+=1
   if len(candidates)!=old:
    last.append({'tested':tested,'remaining':len(candidates),'piece':P,'placements':len(V)})
    print('remaining',len(candidates),'after',tested,flush=True)
   if not candidates:break
  result={'n':11,'radius':r,'container_size':len(D)-4,'conjectured':58,'counts':counts,'initial_candidates':initial,'tested':tested,'survivors':[sorted(H) for H in candidates],'elimination_steps':last,'elapsed':time.monotonic()-start,'seed':260629,'scope':'four interior off-axis holes in D5; no global infeasibility inference'}
  (L/'checks.json').write_text(json.dumps(result,indent=2));print(json.dumps(result),flush=True)
