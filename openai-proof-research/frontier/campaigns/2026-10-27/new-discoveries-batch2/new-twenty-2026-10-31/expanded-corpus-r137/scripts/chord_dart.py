# Check the 2n-dart face model against the 6n half-edge ribbon model (329080).
# dart model: endpoints 0..2n-1; side(i)=mask bit; sigma(i)=next endpoint with same side, inner side in
# increasing cyclic order, outer side in decreasing cyclic order; tau=partner.
# faces = cycles(sigma o tau) + [no inner endpoint] + [no outer endpoint].
import sys,pathlib,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from chord import prep,faces
def words(n):
    def rec(w,nxt):
        if len(w)==2*n: yield tuple(w); return
        if nxt<n: yield from rec(w+[nxt],nxt+1)
        for c in [c for c in range(nxt) if w.count(c)==1]: yield from rec(w+[c],nxt)
    yield from rec([],0)
def dart_faces(w,mask):
    L=len(w); partner=[0]*L; seen={}
    for i,c in enumerate(w):
        if c in seen: partner[i]=seen[c]; partner[seen[c]]=i
        else: seen[c]=i
    side=[(mask>>i)&1 for i in range(L)]
    sig=[0]*L
    for i in range(L):
        s=side[i]; step=1 if s==0 else -1; j=(i+step)%L
        while side[j]!=s: j=(j+step)%L
        sig[i]=j
    vis=[0]*L;f=0
    for i in range(L):
        if not vis[i]:
            f+=1;x=i
            while not vis[x]: vis[x]=1; x=sig[partner[x]]
    f+= (0 in side)==False
    f+= (1 in side)==False
    return f
bad=0;tot=0
for n in range(1,6):
    for w in words(n):
        th=prep(w);L=2*n
        for m in range(1<<L):
            tot+=1
            if faces(th,L,m)!=dart_faces(w,m): bad+=1
print(json.dumps({'checked':tot,'mismatches':bad}))
