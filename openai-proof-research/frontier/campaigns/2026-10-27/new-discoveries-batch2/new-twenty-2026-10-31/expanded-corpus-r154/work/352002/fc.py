# Count fully commutative elements of G(m,m,n) w.r.t. the affine generating set
# s_i=[(i i+1);0] (1<=i<=n-1), s~n=[(1 n);(-1,0,..,0,1)].
# g is FC iff all reduced words lie in one commutation class (commuting = generators commuting in the group).
import sys
from collections import Counter
m=int(sys.argv[1]); n=int(sys.argv[2])
def mul(g,h):
    # element = tuple of (row, weight) per column (0-based)
    return tuple((g[r][0], (g[r][1]+b)%m) for (r,b) in h)
I=tuple((i,0) for i in range(n))
gens=[]
for i in range(n-1):
    g=list(I); g[i]=(i+1,0); g[i+1]=(i,0); gens.append(tuple(g))
g=list(I); g[0]=(n-1,(-1)%m); g[n-1]=(0,1); gens.append(tuple(g))
k=len(gens)
comm=[[mul(gens[a],gens[b])==mul(gens[b],gens[a]) for b in range(k)] for a in range(k)]
# BFS by length; for each element store FC flag and its Foata normal form (tuple of frozensets) if FC
length={I:0}; foata={I:()}; layer=[I]; fc_by_len=[1]; total=1; L=0
def append(F,s):
    j=-1
    for idx in range(len(F)-1,-1,-1):
        if any((not comm[s][t]) for t in F[idx]): j=idx; break
    F=list(F)
    if j+1==len(F): F.append(frozenset([s]))
    else: F[j+1]=F[j+1]|{s}
    return tuple(F)
while layer:
    nxt={}
    for g in layer:
        for s in range(k):
            h=mul(g,gens[s])
            if h in length: continue
            nxt.setdefault(h,[]).append((g,s))
    L+=1
    newlayer=[]; cntfc=0
    for h,preds in nxt.items():
        length[h]=L; newlayer.append(h)
        forms=set(); ok=True
        for (g,s) in preds:
            if foata.get(g) is None: ok=False; break
            forms.add(append(foata[g],s))
            if len(forms)>1: ok=False; break
        foata[h]=next(iter(forms)) if ok else None
        if ok: cntfc+=1
    for g in layer:
        if L-1>0: pass
    layer=newlayer
    if layer: fc_by_len.append(cntfc); total+=cntfc
order=len(length)
print({'m':m,'n':n,'order':order,'fc_total':total,'by_length':fc_by_len,'comm_pairs':[(a,b) for a in range(k) for b in range(a+1,k) if comm[a][b]]})
