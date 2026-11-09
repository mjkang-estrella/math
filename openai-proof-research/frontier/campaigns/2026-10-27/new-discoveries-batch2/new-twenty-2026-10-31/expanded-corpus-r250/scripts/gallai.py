import json,time
start=time.monotonic()
for n in range(1,6):
 edges=[(i,j) for i in range(n) for j in range(i+1,n)];counts=[0]*(1<<len(edges));cs={};total=0
 def run(k,mask):
  global total
  if k==len(edges):counts[mask]+=1;total+=1;return
  i,j=edges[k]
  cs[i,j]=0;run(k+1,mask)
  for c in range(1,4):
   if any(cs.get(tuple(sorted((i,v))),0) and cs.get(tuple(sorted((j,v))),0) and len({c,cs.get(tuple(sorted((i,v))),0),cs.get(tuple(sorted((j,v))),0)})==3 for v in range(n) if v!=i and v!=j):continue
   cs[i,j]=c;run(k+1,mask|1<<k)
  del cs[i,j]
 run(0,0)
 maximum=max(counts);winners=[i for i,v in enumerate(counts) if v==maximum]
 print(json.dumps(dict(n=n,graphs=len(counts),feasible_partial_colourings=total,complete_count=counts[-1],maximum=maximum,unique_complete=winners==[len(counts)-1],wall=time.monotonic()-start)),flush=True)
