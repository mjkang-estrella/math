import json
N=2000000;B=100000;x=bytearray(N)
for i in range(2,N):
 k,r=divmod(i,3);x[i]=x[2*k] if r==0 else x[2*k+1] if r==1 else 1-x[2*k+1]
for length in range(1,33):
 mask=(1<<length)-1;w=0;allwords=set();test=set()
 for i,v in enumerate(x):
  w=((w<<1)|v)&mask
  if i>=length-1:
   allwords.add(w)
   if i<B:test.add(w)
 missing=sorted(w for w in test if mask^w not in allwords)
 print(json.dumps({'length':length,'ambient_prefix':N,'tested_prefix':B,'ambient_distinct':len(allwords),'tested_distinct':len(test),'complements_not_yet_found':missing[:20],'missing_count':len(missing)}),flush=True)
