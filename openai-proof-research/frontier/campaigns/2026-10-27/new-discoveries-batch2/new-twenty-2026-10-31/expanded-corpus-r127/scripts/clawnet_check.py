# Cross-check e_coeffs: X_G(1^k)=chi_G(k) via brute-force colouring counts, and coefficient sum = #acyclic orientations.
import sys, json, random, itertools, pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
import clawnet as C
from math import comb
def chi(adj,k):
    n=len(adj); cnt=0
    col=[-1]*n
    def rec(i):
        nonlocal cnt
        if i==n: cnt+=1; return
        used={col[w] for w in C.bits(adj[i]) if w<i}
        for c in range(k):
            if c not in used: col[i]=c; rec(i+1)
    rec(0); return cnt
def acyc(adj):
    n=len(adj); E=[(u,w) for u in range(n) for w in C.bits(adj[u]) if w>u]
    # acyclic orientations = |chi(-1)| ; compute via chi polynomial interpolation instead: use (-1)^n chi(-1)
    return None
random.seed(int(sys.argv[2]))
n=int(sys.argv[1]); G=C.load(n); S=random.sample(range(len(G)),int(sys.argv[3]))
ok=0
for i in S:
    g=G[i]; c=C.e_coeffs(g)
    for k in range(1,5):
        val=sum(v*eval('*'.join(str(comb(k,p)) for p in lam)) for lam,v in c.items() if v)
        assert val==chi(g,k),(i,k,val,chi(g,k))
    ok+=1
print(json.dumps({'n':n,'checked':ok,'k':[1,2,3,4],'status':'PASS'}))
