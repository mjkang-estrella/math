import itertools as it,time,json,hashlib
import numpy as np
comp=lambda s: ''.join('1' if c=='0' else '0' for c in s)
for d in range(4,13):
 start=time.monotonic();groups={};count=0;potential=[]
 for k in range(3,d):
  for bits in it.product('01',repeat=k):
   f=''.join(bits)
   if f!=min(f,f[::-1],comp(f),comp(f[::-1])):continue
   vs=[x for x in range(2**d) if f not in format(x,f'0{d}b')];N=len(vs);lookup={v:i for i,v in enumerate(vs)}
   adj=np.full((N,d),N,dtype=np.int32)
   for i,x in enumerate(vs):
    near=[lookup[y] for b in range(d) if (y:=x^(1<<b)) in lookup];adj[i,:len(near)]=near
   colors=np.zeros(N+1,dtype=np.int32);colors[:N]=(adj!=N).sum(axis=1)+1;h=hashlib.sha256()
   for _ in range(5):
    signature=np.column_stack((colors[:N],np.sort(colors[adj],axis=1)))
    uniq,inv,counts=np.unique(signature,axis=0,return_inverse=True,return_counts=True)
    h.update(uniq.astype('<i4').tobytes());h.update(counts.astype('<i4').tobytes());colors[:N]=inv+1
   nu=sum(a!=b for a,b in zip(f,f[1:]));count+=1;key=(N,h.digest())
   for old,n in groups.get(key,[]):
    if nu!=n:potential.append([old,f,n,nu])
   groups.setdefault(key,[]).append((f,nu))
 print(json.dumps(dict(d=d,representatives=count,cross_index_invariant_collisions=len(potential),examples=potential[:15],method='Five canonical lexicographic color-refinement rounds, including sorted unique signatures and multiplicities, hashed SHA256; only a necessary isomorphism invariant',seconds=time.monotonic()-start)),flush=True)
