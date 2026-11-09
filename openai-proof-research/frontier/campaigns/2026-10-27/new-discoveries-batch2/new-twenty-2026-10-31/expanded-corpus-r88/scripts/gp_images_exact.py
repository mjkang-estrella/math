# Exhaustive enumeration of all endomorphism images of a non-core non-bipartite G(n,k) whose shortest odd cycles are
# exactly rim cycles of length g (Theorem 2.1(b) of arXiv 2202.06785: non-core <=> no shortest odd cycle uses a spoke;
# a spoke-free cycle is a whole rim). Lemma used: an endomorphism maps a shortest odd cycle C bijectively onto a
# shortest odd cycle (odd closed walk of length g contains an odd cycle of length <= g, hence is a g-cycle).
# So f restricted to each inner rim of length g is an isomorphism onto some rim g-cycle (a dihedral alignment).
# Symmetry: the dihedral subgroup <alpha,beta> of Aut acts on alignments of inner rim 0; we enumerate all alignments
# (no reduction) unless --reduce is given, in which case images are canonicalised under <alpha,beta> afterwards only.
# Outer vertices: f(u_i) in N(f(v_i)), f(u_i)~f(u_{i+1}); all completions enumerated by DFS with memo on image sets.
import sys, json, time, itertools
n=int(sys.argv[1]); k=int(sys.argv[2]); BUDGET=float(sys.argv[3])
from math import gcd
N=2*n; U=lambda i:i%n; V=lambda i:n+i%n
adj=[set() for _ in range(N)]
for i in range(n):
    for a,b in ((U(i),U(i+1)),(U(i),V(i)),(V(i),V(i+k))): adj[a].add(b); adj[b].add(a)
d=gcd(n,k); g=n//d
assert (n%2==1 or k%2==0), 'bipartite'
# rim cycles of length g, as cyclic vertex lists
rims=[[V(j+t*k) for t in range(g)] for j in range(d)]
if n==g: rims.append([U(t) for t in range(n)])
# verify: g is odd girth and no shortest odd cycle uses a spoke is assumed from gp_noncore_list.py output
alignments=[]
for R in rims:
    for s in range(g):
        for e in (1,-1):
            alignments.append(tuple(R[(s+e*t)%g] for t in range(g)))
t0=time.time(); images=set(); count_inner=0; timed_out=False
nbm=[0]*N
for v in range(N):
    for w in adj[v]: nbm[v]|=1<<w
def outer_images(fv):
    # fv: dict inner vertex -> image. Enumerate assignments of u_0..u_{n-1}; collect image sets.
    res=set(); base=0
    for x in fv.values(): base|=1<<x
    memo=set()
    def rec(i, first, prev, img):
        key=(i,first,prev,img)
        if key in memo: return
        memo.add(key)
        if i==n:
            if first in adj[prev]: res.add(img)
            return
        cands=adj[fv[V(i)]]
        for x in cands:
            if i>0 and x not in adj[prev]: continue
            rec(i+1, x if i==0 else first, x, img|(1<<x))
    rec(0,None,None,base)
    return res
# choose alignments for each inner rim j=0..d-1; inner rim j consists of v_{j + t k}, t=0..g-1 in this cyclic order
def dfs(j, fv):
    global count_inner, timed_out
    if time.time()-t0>BUDGET: timed_out=True; return
    if j==d:
        count_inner+=1
        images.update(outer_images(fv)); return
    for al in alignments:
        nf=dict(fv)
        for t in range(g): nf[V(j+t*k)]=al[t]
        # prune: for every column i whose v_i and v_{i+1} are both assigned, need a 3-walk f(v_i)-x-y-f(v_{i+1})
        ok=True
        for i in range(n):
            a,b=V(i),V(i+1)
            if a in nf and b in nf:
                if not any(nbm[x] & nbm[nf[b]] for x in adj[nf[a]]): ok=False; break
        if ok: dfs(j+1, nf)
dfs(0,{})
# retract test for each image
def retract(S):
    assign={v:v for v in range(N) if S>>v&1}
    rest=[v for v in range(N) if v not in assign]
    rest.sort(key=lambda v:-sum(1 for w in adj[v] if w in assign))
    def dom(v):
        D=S
        for w in adj[v]:
            if w in assign: D&=nbm[assign[w]]
        return D
    def rec(i):
        if i==len(rest): return True
        v=rest[i]; D=dom(v)
        while D:
            low=D&-D; x=low.bit_length()-1; D^=low; assign[v]=x
            if all(dom(w) for w in adj[v] if w not in assign) and rec(i+1): return True
            del assign[v]
        return False
    return rec(0)
bad=[]; hist={}
for S in images:
    c=bin(S).count('1'); hist[c]=hist.get(c,0)+1
    if not retract(S): bad.append(S)
nm=lambda S:[('u%d'%v if v<n else 'v%d'%(v-n)) for v in range(N) if S>>v&1]
print(json.dumps({'n':n,'k':k,'d':d,'g':g,'complete':not timed_out,'inner_assignments':count_inner,'distinct_images':len(images),'image_size_histogram':dict(sorted(hist.items())),'num_nonretract_images':len(bad),'nonretract_examples':[nm(S) for S in bad[:3]],'secs':round(time.time()-t0,1)}))
