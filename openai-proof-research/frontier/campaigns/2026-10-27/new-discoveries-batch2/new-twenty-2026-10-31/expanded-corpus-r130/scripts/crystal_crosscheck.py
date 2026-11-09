# Cross-check crystal2.py (this lane) against inherited scripts/crystal.py operator e (0-based roots) on all
# Kostant partitions of size <= S in A_{n-1}.
import sys, json, importlib.util, pathlib
D=pathlib.Path(__file__).resolve().parents[1]
n=int(sys.argv[1]); S=int(sys.argv[2])
sys.argv=['crystal',str(n-1),'0']   # inherited module runs a size-0 loop at import
spec=importlib.util.spec_from_file_location('c',D/'scripts/crystal.py'); c=importlib.util.module_from_spec(spec)
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()): spec.loader.exec_module(c)
sys.path.insert(0,str(D/'scripts'))
from crystal2 import Model
M=Model(n)
# map: inherited roots are combinations(range(n),2) -> (x+1,y+1)
perm=[M.idx[(x+1,y+1)] for (x,y) in c.roots]
def to_mine(a): l=[0]*len(M.roots); [l.__setitem__(perm[j],v) for j,v in enumerate(a)]; return tuple(l)
def to_theirs(al): return tuple(al[perm[j]] for j in range(len(perm)))
def comps(t,k):
    if k==1: yield (t,); return
    for a in range(t+1):
        for r in comps(t-a,k-1): yield (a,)+r
tested=0; bad=[]
for size in range(0,S+1):
    for al in comps(size,len(M.roots)):
        th=to_theirs(al)
        for i in range(1,n):
            mine=M.e(al,i); theirs=c.e(th,i-1)
            tm=(None if mine[0] is None else mine[0], mine[1]); tt=(None if theirs[0] is None else to_mine(theirs[0]), theirs[1])
            tested+=1
            if tm!=tt and len(bad)<5: bad.append(dict(alpha=al,i=i,mine=tm,theirs=tt))
print(json.dumps(dict(n=n,maxsize=S,tested=tested,mismatches=len(bad),first=bad)))
