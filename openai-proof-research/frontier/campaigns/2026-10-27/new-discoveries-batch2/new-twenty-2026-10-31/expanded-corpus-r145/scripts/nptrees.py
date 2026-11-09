# MathDB 338138: every tree is neighborhood-prime (Cloys-Fox). For every free tree of order n
# (WROM generation, re-implemented after the networkx nonisomorphic_trees algorithm), find a bijection
# f:V->[n] with gcd(f(N(v)))=1 for all v of degree>=2, by randomized local search; certificates are
# re-verified independently. Usage: nptrees.py n [start end] ; prints counts and any failures.
import sys,random,math,json,time
def _next_rooted_tree(pred,p=None):
    if p is None:
        p=len(pred)-1
        while pred[p]==1: p-=1
    if p==0: return None
    q=p-1
    while pred[q]!=pred[p]-1: q-=1
    r=list(pred)
    for i in range(p,len(r)): r[i]=r[i-p+q]
    return r
def _split_tree(layout):
    one=False; m=None
    for i in range(len(layout)):
        if layout[i]==1:
            if one: m=i;break
            one=True
    if m is None: m=len(layout)
    return [layout[i]-1 for i in range(1,m)],[0]+[layout[i] for i in range(m,len(layout))]
def _next_tree(c):
    left,rest=_split_tree(c)
    lh=max(left); rh=max(rest); valid=rh>=lh
    if valid and rh==lh:
        if len(left)>len(rest): valid=False
        elif len(left)==len(rest) and left>rest: valid=False
    if valid: return c
    p=len(left); nc=_next_rooted_tree(c,p)
    if c[p]>2:
        nl,nr=_split_tree(nc); nlh=max(nl); suf=list(range(1,nlh+2))
        nc[-len(suf):]=suf
    return nc
def trees(n):
    layout=list(range(n//2+1))+list(range(1,(n+1)//2))
    while layout is not None:
        layout=_next_tree(layout)
        if layout is not None:
            yield layout
            layout=_next_rooted_tree(layout)
def adj_from_layout(lay):
    n=len(lay); adj=[[] for _ in range(n)]; stack=[]
    for i,d in enumerate(lay):
        while len(stack)>d: stack.pop()
        if stack: adj[i].append(stack[-1]); adj[stack[-1]].append(i)
        stack.append(i)
    return adj
def bad_vertices(adj,f):
    return [v for v in range(len(adj)) if len(adj[v])>=2 and math.gcd(*[f[u] for u in adj[v]])!=1]
def search(adj,rng,tries=200,steps=2000):
    n=len(adj)
    inner=[v for v in range(n) if len(adj[v])>=2]
    for t in range(tries):
        f=list(range(1,n+1)); rng.shuffle(f)
        badset=set(bad_vertices(adj,f))
        for s in range(steps):
            if not badset: return f
            v=rng.choice(sorted(badset)); u=rng.choice(adj[v]); w=rng.randrange(n)
            # swap labels of u and w; recompute affected vertices
            aff={x for x in adj[u]}|{x for x in adj[w]}
            old=sum(1 for x in aff if x in badset)
            f[u],f[w]=f[w],f[u]
            newbad={x for x in aff if len(adj[x])>=2 and math.gcd(*[f[y] for y in adj[x]])!=1}
            if len(newbad)<=old or rng.random()<0.05:
                badset=(badset-aff)|newbad
            else:
                f[u],f[w]=f[w],f[u]
    return None
if __name__=='__main__':
    n=int(sys.argv[1]); a=int(sys.argv[2]) if len(sys.argv)>2 else 0; b=int(sys.argv[3]) if len(sys.argv)>3 else 10**9
    rng=random.Random(12345+n); cnt=done=0; fails=[]; t0=time.time()
    for idx,lay in enumerate(trees(n)):
        cnt+=1
        if idx<a or idx>=b: continue
        adj=adj_from_layout(lay)
        f=search(adj,rng)
        if f is None: fails.append(lay)
        else:
            assert sorted(f)==list(range(1,n+1)) and not bad_vertices(adj,f)
        done+=1
    print(json.dumps(dict(n=n,total_trees=cnt,range=[a,min(b,cnt)],checked=done,fails=len(fails),fail_layouts=fails[:10],sec=round(time.time()-t0,1))),flush=True)
