import random,json,pathlib,sys,time
L=pathlib.Path(__file__).resolve().parents[1]; rng=random.Random(148)
def solve(M,limit):
 n=len(M);k=len(M[0]);counts=[x for row in M for x in row];full=(1<<(n*k))-1;nodes=0;trace=[]
 def rec(todo):
  nonlocal nodes
  nodes+=1
  if nodes>limit:raise TimeoutError
  if not todo:return True
  best=None
  for a in range(n):
   for d in range(k):
    cell=a*k+d
    if not(todo>>cell&1):continue
    opts=[]
    if counts[cell]:opts.append((cell,cell,cell,cell))
    for c in range(n):
     if c==a or not counts[c*k+d]:continue
     for b in range(k):
      other=c*k+b
      if b!=d and counts[a*k+b] and todo>>other&1:opts.append((a*k+b,c*k+d,cell,other))
    if not opts:return False
    if best is None or len(opts)<len(best):best=opts
  best.sort(key=lambda t:-(counts[t[0]]+counts[t[1]]))
  for s,t,u,v in best:
   counts[s]-=1
   if s!=t:counts[t]-=1
   trace.append((s,t,u,v))
   if rec(todo & ~(1<<u) & ~(1<<v)):return True
   trace.pop();counts[s]+=1
   if s!=t:counts[t]+=1
  return False
 try: ok=rec(full);return {'status':'SAT' if ok else 'UNSAT','nodes':nodes,'certificate':trace.copy()}
 except TimeoutError:return {'status':'UNKNOWN_NODE_LIMIT','nodes':nodes}
out=[]
for n,k,reps in [(3,3,30),(6,9,300),(7,10,300),(8,11,300),(9,12,300)]:
 for trial in range(reps):
  colors=list(range(k))*n;rng.shuffle(colors);M=[[colors[a*k:(a+1)*k].count(b) for b in range(k)] for a in range(n)]
  r=solve(M,20000);r.update(n=n,k=k,trial=trial,matrix=M);out.append(r)
  if r['status']!='SAT':print(r,flush=True)
 print(n,k,'done',reps,flush=True)
 (L/'outputs/petrov.json').write_text(json.dumps(out))
