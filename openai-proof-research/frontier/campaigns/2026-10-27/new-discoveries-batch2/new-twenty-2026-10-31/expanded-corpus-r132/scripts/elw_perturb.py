# Hill-climb ELW objective starting from equality configurations: disjoint unions of <=w complete w-partite graphs.
import sys,random,json,math
import numpy as np
sys.path.insert(0,__file__.rsplit('/',1)[0])
from elw_local import clique_number
def f(A):
    m=A.sum()/2; ev=np.sort(np.linalg.eigvalsh(A))[::-1]; npos=int((ev>1e-9).sum())
    w=clique_number(A); l=min(npos,w); return (ev[:l]**2).sum()/m-2*(1-1/w),w,npos
seed=int(sys.argv[1]); W=int(sys.argv[2]); a=int(sys.argv[3]); iters=int(sys.argv[4]); rnd=random.Random(seed)
best=(-9,None)
for rep in range(200):
    parts=[]; n=0
    for c in range(W):
        sizes=[rnd.randint(1,a) for _ in range(W)]; parts.append([list(range(n+sum(sizes[:i]),n+sum(sizes[:i+1]))) for i in range(W)]); n+=sum(sizes)
    A=np.zeros((n,n),int)
    for comp in parts:
        for i in range(W):
            for j in range(i+1,W):
                for x in comp[i]:
                    for y in comp[j]: A[x,y]=A[y,x]=1
    cur=f(A)[0]
    for it in range(iters):
        x,y=rnd.sample(range(n),2); A[x,y]^=1; A[y,x]^=1
        if A.sum()==0: A[x,y]^=1; A[y,x]^=1; continue
        v,w,npos=f(A)
        if w==W and v>=cur-1e-12: cur=v
        else: A[x,y]^=1; A[y,x]^=1
    if cur>best[0]:
        best=(cur,n); print(rep,'best',cur,n,flush=True)
        if cur>1e-9: print('VIOL',np.argwhere(np.triu(A)).tolist(),flush=True); break
