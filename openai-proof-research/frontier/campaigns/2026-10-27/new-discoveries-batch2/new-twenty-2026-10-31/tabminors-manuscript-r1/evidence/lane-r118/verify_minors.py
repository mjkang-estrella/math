"""Independent exact check (pure Python, own jeu de taquin from scripts/minors.py) of multiset collisions mM_k(T)=mM_k(T')."""
import sys, functools
from collections import Counter
sys.path.insert(0,'scripts'); from minors import delete
def decode(key,n):
    rows={}
    for e in range(1,n+1):
        r=(key>>(4*(e-1)))&15; rows.setdefault(r,[]).append(e)
    return tuple(tuple(rows[r]) for r in sorted(rows))
def is_syt(T,n):
    ents=sorted(x for r in T for x in r)
    if ents!=list(range(1,n+1)): return False
    if any(len(T[i])<len(T[i+1]) for i in range(len(T)-1)): return False
    if any(T[i][j]>=T[i][j+1] for i in range(len(T)) for j in range(len(T[i])-1)): return False
    if any(T[i][j]>=T[i+1][j] for i in range(len(T)-1) for j in range(len(T[i+1]))): return False
    return True
@functools.lru_cache(maxsize=None)
def mm(T,k):
    if k==0: return ((T,1),)
    n=sum(len(r) for r in T); C=Counter()
    for m in range(1,n+1):
        for t,c in mm(delete(T,m),k-1): C[t]+=c
    return tuple(sorted(C.items()))
if __name__=='__main__':
    n,k=int(sys.argv[1]),int(sys.argv[2])
    for a,b in zip(sys.argv[3::2],sys.argv[4::2]):
        T,U=decode(int(a,16),n),decode(int(b,16),n)
        A,B=mm(T,k),mm(U,k)
        print('T =',T,'\nU =',U,'\n SYT:',is_syt(T,n),is_syt(U,n),' distinct:',T!=U,' |mM_k| =',sum(c for _,c in A),sum(c for _,c in B),' equal multisets:',A==B)
        if A==B: print(' common multiset:',A)
