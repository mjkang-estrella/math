# Exact check of Garcia-Marco--Knauer Conjecture 4.1 (arXiv 2202.06785) for small non-bipartite G(n,k):
# "the image of any endomorphism is a retract".  Image of f = vertex set f(V); retract = induced subgraph G[S]
# admitting a homomorphism r: G -> G[S] with r|S = id (source Section 2 definitions).
# Method: for every vertex subset S (up to the dihedral rotations/reflections), if S is NOT a retract,
# test whether S is the exact image of some endomorphism (homomorphism G -> G[S] onto S).
import sys, json, time
from math import gcd
n=int(sys.argv[1]); k=int(sys.argv[2])
N=2*n
adj=[set() for _ in range(N)]
def E(a,b): adj[a].add(b); adj[b].add(a)
for i in range(n):
    E(i,(i+1)%n); E(i,n+i); E(n+i,n+(i+k)%n)
nb=[0]*N
for v in range(N):
    for w in adj[v]: nb[v]|=1<<w
assert all(len(a)==3 for a in adj), 'not cubic'
bip = (n%2==0 and k%2==1)
# dihedral symmetries alpha, beta as vertex permutations
def rot(t): return [ (i+t)%n for i in range(n)] + [n+(i+t)%n for i in range(n)]
def ref(): return [(-i)%n for i in range(n)] + [n+(-i)%n for i in range(n)]
perms=[]
for t in range(n):
    r=rot(t); perms.append(r); b=ref(); perms.append([r[b[v]] for v in range(N)])
def apply(p,S):
    T=0
    for v in range(N):
        if S>>v&1: T|=1<<p[v]
    return T
def bits(S): return [v for v in range(N) if S>>v&1]
def is_hom_search(S, fixed, surj):
    # assign each vertex a value in S; fixed: vertices of S mapped to themselves (retraction); surj: require image == S
    order=[]; seen=set()
    start=[v for v in range(N) if fixed and S>>v&1] or [0]
    queue=list(start); 
    for v in start: seen.add(v)
    while queue:
        v=queue.pop(0); order.append(v)
        for w in sorted(adj[v]):
            if w not in seen: seen.add(w); queue.append(w)
    assign={}
    if fixed:
        for v in bits(S): assign[v]=v
    rest=[v for v in order if v not in assign]
    Sl=bits(S); Ssize=len(Sl)
    def dom(v):
        D=S
        for w in adj[v]:
            if w in assign: D&=nb[assign[w]]
        return D
    def rec(i, covered):
        if surj and Ssize-bin(covered).count('1') > len(rest)-i: return False
        if i==len(rest): return (not surj) or covered==S
        v=rest[i]; D=dom(v)
        while D:
            low=D&-D; x=low.bit_length()-1; D^=low
            assign[v]=x
            # forward check unassigned neighbours
            ok=True
            for w in adj[v]:
                if w not in assign and dom(w)==0: ok=False; break
            if ok and rec(i+1, covered|low): return True
            del assign[v]
        return False
    return rec(0, 0)
def connected(S):
    if S==0: return False
    start=S&-S; seen=start; frontier=start
    while frontier:
        new=0
        for v in bits(frontier): new|=nb[v]&S
        new&=~seen; seen|=new; frontier=new
    return seen==S
# Every image contains an odd cycle of length g = odd girth (image of a shortest odd cycle is an odd closed
# walk of length <= g, hence contains an odd cycle of length exactly g). Enumerate S = (g-cycle) ∪ T.
import itertools
def odd_girth_cycles():
    # all cycles (as vertex bitmasks) of minimum odd length, by DFS from each start vertex
    best=None; cyc=set()
    for L in range(3,N+1,2):
        for s0 in range(N):
            stack=[(s0,[s0])]
            while stack:
                v,path=stack.pop()
                if len(path)==L:
                    if s0 in adj[v]:
                        cyc.add(sum(1<<x for x in path))
                    continue
                for w in adj[v]:
                    if w>s0 and w not in path: stack.append((w,path+[w]))
        if cyc: return L,sorted(cyc)
g,cycles=odd_girth_cycles()
t=time.time(); checked=0; nonretract=set(); counter=[]; retracts=set(); visited=set()
for c in cycles:
    comp=[v for v in range(N) if not c>>v&1]
    for r in range(len(comp)+1):
        for T in itertools.combinations(comp,r):
            S=c|sum(1<<x for x in T)
            if S in visited: continue
            visited.add(S)
            if not connected(S): continue
            checked+=1
            if is_hom_search(S, True, False):
                retracts.add(min(apply(p,S) for p in perms)); continue
            cs=min(apply(p,S) for p in perms)
            if cs in nonretract: continue
            nonretract.add(cs)
            if is_hom_search(S, False, True):
                counter.append(bits(S))
names=lambda L:[("u%d"%v if v<n else "v%d"%(v-n)) for v in L]
_unused=lambda L:[('u%d'%v if v<n else 'v%d'%(v-n)) for v in L]
print(json.dumps({'n':n,'k':k,'bipartite':bip,'odd_girth':g,'num_min_odd_cycles':len(cycles),'connected_subsets_containing_min_odd_cycle':checked,'retract_classes':len(retracts),'retract_class_examples':[names(bits(x)) for x in sorted(retracts,key=lambda x:bin(x).count('1'))[:6]],'nonretract_classes':len(nonretract),'nonretract_images_counterexamples':[names(c) for c in counter[:5]],'num_counterexamples':len(counter),'secs':round(time.time()-t,2)}))
