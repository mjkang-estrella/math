# Chunked test of the extension conjecture for J=6, I=4 (N=30): Golomb 6-subsets A1 of [30], indexed in lexicographic order.
import sys,itertools,time,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).parent))
from dgr import golomb,partition,rulers_containing
J,I=6,4; N=30
lo,hi=int(sys.argv[1]),int(sys.argv[2])
# enumerate Golomb 6-subsets lexicographically via rulers_containing per minimum element
allA=[]
for x in range(1,N+1):
    allA+=rulers_containing(x,list(range(1,N+1)),J)
if lo==0: print('total golomb 6-subsets of [30]:',len(allA),flush=True)
t=time.time(); bad=0; done=0
for A in allA[lo:hi]:
    rem=[y for y in range(1,N+1) if y not in A]
    if partition(rem,J) is None: print('NO EXTENSION',A,flush=True); bad+=1
    done+=1
    if time.time()-t>125: break
print('range',lo,lo+done,'failures',bad,'%.1fs'%(time.time()-t))
