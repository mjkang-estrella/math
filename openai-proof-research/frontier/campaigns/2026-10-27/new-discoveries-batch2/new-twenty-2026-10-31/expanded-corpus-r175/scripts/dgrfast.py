# Bitmask exact cover for regular DGR extension (arXiv:2409.14409 Conjecture genefirstnb), with a shared memo of solvable masks.
import sys,time,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).parent))
from dgr import rulers_containing
sys.setrecursionlimit(10000)
J,I=int(sys.argv[1]),int(sys.argv[2]); N=(I+1)*J
lo=int(sys.argv[3]) if len(sys.argv)>3 else 0; hi=int(sys.argv[4]) if len(sys.argv)>4 else 10**9
bymin={x:[sum(1<<(y-1) for y in R) for R in rulers_containing(x,list(range(1,N+1)),J)] for x in range(1,N+1)}
allA=[m for x in range(1,N+1) for m in bymin[x]]
memo={0:True}
def solvable(mask):
    r=memo.get(mask)
    if r is not None: return r
    x=(mask&-mask).bit_length()
    r=False
    for R in bymin[x]:
        if R&mask==R and solvable(mask^R): r=True;break
    memo[mask]=r
    return r
full=(1<<N)-1
t=time.time(); bad=[]; done=0
print('J',J,'I',I,'N',N,'golomb A1 total',len(allA),flush=True)
for A in allA[lo:hi]:
    if not solvable(full^A): bad.append(A); print('NO EXTENSION',[y+1 for y in range(N) if A>>y&1],flush=True)
    done+=1
    if time.time()-t>120: break
print('range',lo,lo+done,'failures',len(bad),'memo',len(memo),'%.1fs'%(time.time()-t))
