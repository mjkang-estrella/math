import itertools,json,collections,time
start=time.time();rows=[]
# Direct 0/1-fillings, independent of the permutation bridge.
for n in range(1,8):
 counts=[0]*(n+1);shapes=0;candidates=0
 for r in range(1,n+1):
  c=n+1-r
  for tail in itertools.combinations_with_replacement(range(1,c+1),r-1):
   shape=(c,)+tuple(reversed(tail));shapes+=1
   cells=[(i,j) for i in range(1,r) for j in range(shape[i])]
   for m in range(1<<len(cells)):
    candidates+=1;mat=[[1]*c]+[[0]*z for z in shape[1:]]
    for k,(i,j) in enumerate(cells):mat[i][j]=m>>k&1
    if any(all(row) for row in mat[1:]):continue
    ok=True
    for i in range(1,r):
     for h in range(1,i):
      types={2*mat[h][j]+mat[i][j] for j in range(shape[i])}
      if 1 in types and 2 in types:ok=False;break
     if not ok:break
    if ok:counts[sum(any(j<len(row) and row[j]==0 for row in mat) for j in range(c))]+=1
 euler=[0]*(n+1)
 for p in itertools.permutations(range(1,n+1)):euler[sum(v>i+1 for i,v in enumerate(p))]+=1
 rows.append({'n':n,'shapes':shapes,'fillings_examined':candidates,'counts':counts,'eulerian':euler,'equal':counts==euler})
print(json.dumps({'rows':rows,'seconds':time.time()-start}))
