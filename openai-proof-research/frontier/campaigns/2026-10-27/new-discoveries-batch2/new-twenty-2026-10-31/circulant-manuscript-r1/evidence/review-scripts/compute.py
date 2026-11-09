import itertools as it,json,pathlib,random,time
W=pathlib.Path(__file__).resolve().parents[1]
def graph(n,pos):
 S={x%n for d in pos for x in (d,-d)}-{0}
 return [{(v+d)%n for d in S} for v in range(n)]
def radius(A):return len({0}|A[0]|set().union(*(A[v] for v in A[0])))==len(A)
def triangle(A):return any(A[0]&A[v] for v in A[0])
def paths(A,visit,cap=500000):
 count=0;done=False
 def walk(p):
  nonlocal count,done
  count+=1
  if count>cap:return
  if visit(p):done=True;return
  forbidden=set(p)
  for x in p[:-1]:forbidden.update(A[x])
  for y in sorted(A[p[-1]]-forbidden):
   walk(p+[y])
   if done or count>cap:return
 walk([0]);return count,done,count<=cap

def orbit(t,n):return min(tuple(sorted((v-a)%n for v in t)) for a in t)
def mp2(n,pos):
 A=graph(n,pos)
 if triangle(A) or not radius(A):return None
 missing={orbit((0,a,b),n) for a in range(1,n) for b in range(a+1,n)};witness={}
 def visit(p):
  for t in it.combinations(p[:-1],2):
   k=orbit((*t,p[-1]),n)
   if k in missing:missing.remove(k);witness[str(k)]=p[:]
  return not missing
 count,done,complete=paths(A,visit)
 return {'n':n,'positive_jumps':list(pos),'mp':2 if done else None,'nodes':count,'complete_path_enumeration':complete,'uncovered_orbits':len(missing),'witnesses':witness}
def exact(n,pos):
 A=graph(n,pos);bad=set()
 def visit(p):
  for t in it.combinations(p[:-1],2):
   for a in range(n):bad.add(sum(1<<((x+a)%n) for x in (*t,p[-1])))
  return False
 count,_,complete=paths(A,visit,2000000)
 assert complete
 # Every forbidden triple has now been enumerated. Find largest avoiding subset.
 for k in range(n,1,-1):
  for t in it.combinations(range(n),k):
   mask=sum(1<<x for x in t)
   if not any(mask&b==b for b in bad):return dict(n=n,positive_jumps=list(pos),mp=k,maximum_set=t,forbidden_triples=len(bad),path_nodes=count)
rows=[];counts={};residual=[]
for m in range(128):
 pos=[d for d in range(1,8) if m>>(d-1)&1];A=graph(15,pos)
 label='triangle' if triangle(A) else ('distance_obstruction' if not radius(A) else 'residual')
 counts[label]=counts.get(label,0)+1
 if label=='residual':
  assert A[0]==A[5]==A[10];residual.append(exact(15,pos))
 rows.append(dict(mask=m,positive_jumps=pos,label=label))
(W/'classification.json').write_text(json.dumps(dict(counts=counts,rows=rows,residual=residual),indent=2))
print('classification',counts,residual,flush=True)
samples=[exact(15,p) for p in [[],[1],[1,2,3,4,5,6,7],[1,2]]]
(W/'exact-samples.json').write_text(json.dumps(samples,indent=2));print('samples',samples,flush=True)
coverage=[];rng=random.Random(350979)
for n in range(11,41):
 if n==15:coverage.append(dict(n=n,exists=False,all_masks=128));continue
 seen=set();found=None;trials=0
 candidates=it.chain([tuple(range(n//3+1,n//2+1))],it.combinations(range(1,n//2+1),2),it.combinations(range(1,n//2+1),3),it.combinations(range(1,n//2+1),4),(tuple(sorted(rng.sample(range(1,n//2+1),rng.randrange(3,max(4,n//3))))) for _ in range(2000)))
 for pos in candidates:
  if pos in seen:continue
  seen.add(pos);trials+=1
  r=mp2(n,pos)
  if r and r['mp']==2:found=r;break
 coverage.append(dict(n=n,trials=trials,exists=True if found else None,certificate=found))
 (W/'coverage.json').write_text(json.dumps(coverage,indent=2));print(n,trials,found['positive_jumps'] if found else None,flush=True)
