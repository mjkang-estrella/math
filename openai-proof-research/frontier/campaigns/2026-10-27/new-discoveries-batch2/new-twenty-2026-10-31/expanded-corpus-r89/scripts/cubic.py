import itertools,json,time
start=time.monotonic()
def twofh(rows,m):
 good=True;total=0;bad=None
 def rec(i,used,matching):
  nonlocal good,total,bad
  if not good:return
  if i==m:
   total+=1;a=[[] for _ in range(2*m)]
   for u,row in enumerate(rows):
    for v in row:
     if matching[u]!=v:a[u].append(m+v);a[m+v].append(u)
   seen={0};q=[0]
   for u in q:
    for v in a[u]:
     if v not in seen:seen.add(v);q.append(v)
   if len(seen)!=2*m:good=False;bad=matching
   return
  for v in rows[i]:
   if not used>>v&1:rec(i+1,used|1<<v,matching+[v])
 rec(0,0,[]);return good,total,bad
for m in [7,8]:
 triples=list(itertools.combinations(range(m),3));rows=[triples[0]];deg=[int(v<3) for v in range(m)];counts=[0,0];examples=[]
 def rec(last):
  if len(rows)==m:
   if any(d!=3 for d in deg):return
   counts[0]+=1;good,total,bad=twofh(rows,m)
   if good:counts[1]+=1;examples.append([list(t) for t in rows])
   return
  for ix in range(last+1,len(triples)):
   t=triples[ix]
   if any(deg[v]>=3 for v in t) or any(len(set(t)&set(s))>1 for s in rows):continue
   rows.append(t)
   for v in t:deg[v]+=1
   if all(d+(m-len(rows))>=3 for d in deg):rec(ix)
   for v in t:deg[v]-=1
   rows.pop()
 rec(0)
 print(json.dumps(dict(m=m,normalized_girth6_row_systems=counts[0],two_factor_hamiltonian=counts[1],examples=examples)),flush=True)
# All normalized three-shift circulants through 30 vertices.
counts=[0,0];survivors=[]
for m in range(7,16):
 for x,y in itertools.combinations(range(1,m),2):
  rows=[tuple(sorted([i,(i+x)%m,(i+y)%m])) for i in range(m)]
  if any(len(set(a)&set(b))>1 for a,b in itertools.combinations(rows,2)):continue
  counts[0]+=1;good,total,_=twofh(rows,m)
  if good:counts[1]+=1;survivors.append([m,x,y,total])
print(json.dumps(dict(circulants_girth6=counts[0],twofh=counts[1],survivors=survivors)),flush=True)
