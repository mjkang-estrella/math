import json,time
start=time.time();out=[]
for k in range(2,72):
 primes=[p for p in range(2,k+1) if all(p%d for d in range(2,int(p**.5)+1))]
 # Enough to compute every k through 40, then the published endpoint k=71.
 if k>40 and k!=71:continue
 size=1<<len(primes);c=[0]*size
 for x in range(2,k+1):
  mask=sum(1<<j for j,p in enumerate(primes) if x%p==0);c[mask]+=1
 for bit in range(len(primes)):
  h=1<<bit
  for block in range(0,size,2*h):
   for j in range(block,block+h):c[j+h]+=c[j]
 best=0;witness=0;full=size-1
 for mask in range(size):
  val=min(c[mask],1+c[full^mask])
  if val>best:best=val;witness=mask
 out.append({'k':k,'max_balanced_part_size':best,'prime_set':[p for j,p in enumerate(primes) if witness>>j&1],'prime_partitions':size})
print(json.dumps({'rows':out,'seconds':time.time()-start}))
