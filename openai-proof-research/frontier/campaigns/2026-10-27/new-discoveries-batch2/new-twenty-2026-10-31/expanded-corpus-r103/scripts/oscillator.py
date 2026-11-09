import itertools as it,random,math,json,numpy as np
from pathlib import Path
D=Path(__file__).resolve().parents[1];rng=random.Random(103);rows=[]
for N in [3,4]:
 seqs=[(0,)+s for s in it.combinations(range(1,8),4)];jumps=[]
 for j in range(1,5):jumps.append((math.comb(N+j-1,N)+1,math.comb(N+j-1,N-1)))
 maxima={k:0 for k,m in jumps};bad=[];count=0
 tests=it.combinations_with_replacement(seqs,N) if N==3 else (tuple(tuple([0]+sorted(rng.sample(range(1,15),6))) for _ in range(N)) for z in range(20000))
 for arrays in tests:
  a=np.array([0])
  for seq in arrays:a=(a[:,None]+seq).ravel()
  hist=np.bincount(a);less=0;count+=1
  for val,mult in enumerate(hist):
   if not mult:continue
   for k,expected in jumps:
    if less<k<=less+int(mult):
     maxima[k]=max(maxima[k],int(mult))
     if mult>expected:bad.append(dict(arrays=arrays,k=k,level=val,less=less,multiplicity=int(mult),oscillator=expected))
   less+=int(mult)
  if bad:break
 rows.append(dict(N=N,instances=count,jumps=jumps,maxima=maxima,counterexamples=bad,tail='Each row continued with strictly increasing integers above maximum tested sum; finite multiplicities realized by admissible infinite arrays'))
 print(rows[-1],flush=True)
(D/'outputs/oscillator.json').write_text(json.dumps(rows,indent=2)+'\n')
