# Regularity of (I,J,IJ)-DGR by bitmask exact cover (exhaustive when no solution).
import sys,time,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).parent))
from dgr import rulers_containing
J,I=int(sys.argv[1]),int(sys.argv[2]); N=I*J
t=time.time()
bymin={x:[sum(1<<(y-1) for y in R) for R in rulers_containing(x,list(range(1,N+1)),J)] for x in range(1,N+1)}
print('J',J,'I',I,'rulers',sum(map(len,bymin.values())),'%.1fs'%(time.time()-t),flush=True)
memo={0:True}; sol={}
def solvable(mask):
    r=memo.get(mask)
    if r is not None: return r
    x=(mask&-mask).bit_length(); r=False
    for R in bymin[x]:
        if R&mask==R and solvable(mask^R): r=True; sol[mask]=R; break
    memo[mask]=r; return r
ok=solvable((1<<N)-1)
out=[]; m=(1<<N)-1
while ok and m:
    R=sol[m]; out.append([y+1 for y in range(N) if R>>y&1]); m^=R
print('J',J,'I',I,'regular' if ok else 'NOT regular (exhaustive)',out,'memo',len(memo),'%.1fs'%(time.time()-t))
