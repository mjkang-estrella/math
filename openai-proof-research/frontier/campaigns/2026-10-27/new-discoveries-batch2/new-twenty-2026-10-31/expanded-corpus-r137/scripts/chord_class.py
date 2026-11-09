# List the class C_n (max genus <= 2) with genus ranges, n <= N.
import sys,json,random,time,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from chord import canon,prep,faces
N=int(sys.argv[1])
def rng_full(w,cap=2):
    L=len(w); n=L//2; theta=prep(w); gs=set()
    for mask in range(0,1<<L,2):
        g=(2+n-faces(theta,L,mask))//2; gs.add(g)
        if g>cap: return None
    return gs
C={(0,0):{0,1}}
for n in range(2,N+1):
    cand=set()
    for w in C:
        L=len(w)
        for i in range(L+1):
            for j in range(i,L+1):
                u=list(w); u.insert(j,n-1); u.insert(i,n-1); cand.add(canon(tuple(u)))
    C={}
    for w in cand:
        gs=rng_full(w)
        if gs is not None: C[w]=gs
    print('n=',n,len(C))
    for w,gs in sorted(C.items()): print('  ',''.join(chr(97+c) for c in w),sorted(gs))
