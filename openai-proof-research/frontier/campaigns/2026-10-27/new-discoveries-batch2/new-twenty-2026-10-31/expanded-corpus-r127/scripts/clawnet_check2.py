# brute-force stable set partition types vs DP, on sampled graphs
import sys, json, random, pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
import clawnet as C
def setparts(lst):
    if not lst: yield []; return
    f=lst[0]
    for p in setparts(lst[1:]):
        for i in range(len(p)): yield p[:i]+[[f]+p[i]]+p[i+1:]
        yield [[f]]+p
random.seed(5); n=int(sys.argv[1]); G=C.load(n); S=random.sample(range(len(G)),int(sys.argv[2]))
for i in S:
    g=G[i]; br={}
    for p in setparts(list(range(n))):
        if all(not (g[u]>>w)&1 for B in p for u in B for w in B):
            lam=tuple(sorted((len(B) for B in p),reverse=True)); br[lam]=br.get(lam,0)+1
    assert br==C.stable_types(g),i
print(json.dumps({'n':n,'checked':len(S),'status':'PASS'}))
