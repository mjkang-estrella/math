# 334831 exploration: graphs with a partition into alpha cliques each having a simplicial vertex
# (well-covered by construction). alpha=6, n<=16, window {3,4,5}; search for a 'dip' s4<s3, s4<s5
# and other orders by randomized hill climbing. Diagnostic only.
import random,itertools,sys,json,time
A=6; NMAX=int(sys.argv[1]); seed=int(sys.argv[2]); rng=random.Random(seed)
def indep_poly(n,adj):
    # count independent sets by size via bitmask recursion
    s=[0]*(n+1)
    def rec(i,mask,k):
        if i==n: s[k]+=1; return
        rec(i+1,mask,k)
        if not (mask>>i)&1: rec(i+1,mask|adj[i],k+1)
    rec(0,0,0); return s
def build(sizes,extra):
    # clique i: simplicial vertex + sizes[i] non-simplicial vertices; extra = set of edges between
    # non-simplicial vertices of different cliques
    n=0;cl=[];ns=[]
    for t in sizes:
        vs=list(range(n,n+1+t)); cl.append(vs); ns.append(vs[1:]); n+=1+t
    adj=[0]*n
    for vs in cl:
        for a in vs:
            for b in vs:
                if a!=b: adj[a]|=1<<b
    for a,b in extra: adj[a]|=1<<b; adj[b]|=1<<a
    return n,adj,ns
def score(s,target):
    # target: permutation of (3,4,5) meaning s[t0]<s[t1]<s[t2]; margin
    return min(s[target[i+1]]-s[target[i]] for i in range(2))
found={}
t0=time.time()
targets=list(itertools.permutations((3,4,5)))
while time.time()-t0<100:
    tot=rng.randint(NMAX-6-2,NMAX-6)
    sizes=[0]*A
    for _ in range(tot): sizes[rng.randrange(A)]+=1
    n,adj,ns=build(sizes,[])
    pairs=[(a,b) for i in range(A) for j in range(i+1,A) for a in ns[i] for b in ns[j]]
    E=set(e for e in pairs if rng.random()<rng.random())
    tgt=rng.choice(targets)
    def f(E):
        n,adj,_=build(sizes,E); s=indep_poly(n,adj); return score(s,tgt),s,n
    cur,s,n=f(E)
    for it in range(150):
        if not pairs: break
        e=rng.choice(pairs); E2=set(E); E2.symmetric_difference_update({e})
        v,s2,_=f(E2)
        if v>=cur: E,cur,s=E2,v,s2
        if cur>0: break
    if cur>0:
        key=''.join(map(str,tgt))
        if key not in found: found[key]={'n':n,'sizes':sizes,'edges':sorted(E),'s':s}; print(key,n,s,flush=True)
    if len(found)==6: break
print(json.dumps({'nmax':NMAX,'found_orders':sorted(found)}))
json.dump(found,open(f'outputs/roller-a6-n{NMAX}-s{seed}.json','w'))
