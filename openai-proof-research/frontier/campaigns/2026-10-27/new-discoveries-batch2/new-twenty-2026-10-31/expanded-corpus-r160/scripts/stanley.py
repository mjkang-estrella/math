# Chan-Pak-Panova matching conjecture (arXiv:2205.02798v3, Sec. 10 "Injections and matchings"):
# G=(V u W,E), V=E(P,x,a)^2, W=E(P,x,a-1)xE(P,x,a+1). For (pi,sigma) in W and y with pos_pi(y)>a-1, pos_sigma(y)<a+1
# (positions 1-based), edge to (demote_pi_from_pos_i, promote_sigma_from_pos_j). Check a matching saturating W.
import sys,itertools,time
def posets(n):
    # naturally labelled posets on 0..n-1 (i<j whenever i<j in poset), as list of up-sets bitmasks (transitively closed)
    pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
    res=[]
    def rec(k,lt):
        if k==len(pairs):
            res.append(lt[:]); return
        i,j=pairs[k]
        # option not related (only if not forced by transitivity)
        forced=any((lt[i]>>m&1) and (lt[m]>>j&1) for m in range(i+1,j))
        if not forced: rec(k+1,lt)
        old=lt[i]; lt[i]|=1<<j
        # transitivity: anything below i (already processed i'<i with j'..) -- we process pairs in order (i asc, j asc);
        # closure check done at end instead
        rec(k+1,lt); lt[i]=old
    rec(0,[0]*n)
    out=[]
    for lt in res:
        ok=True
        for a in range(n):
            for b in range(n):
                if lt[a]>>b&1:
                    if (lt[a]|lt[b])!=lt[a]: ok=False
        if ok: out.append(tuple(lt))
    return sorted(set(out))
def linexts(n,lt):
    below=[0]*n
    for a in range(n):
        for b in range(n):
            if lt[a]>>b&1: below[b]|=1<<a
    res=[]
    def rec(placed,word):
        if len(word)==n: res.append(tuple(word)); return
        for v in range(n):
            if not placed>>v&1 and (below[v]&~placed)==0:
                word.append(v); rec(placed|1<<v,word); word.pop()
    rec(0,[]); return res
def less(lt,u,v): return lt[u]>>v&1
def demote(w,i,lt):
    # left action of tau_1...tau_{i-1} (apply tau_{i-1} first): moving element starts at 0-based position i-1, goes down
    w=list(w); p=i-1
    for q in range(p-1,-1,-1):  # tau at positions (q,q+1)
        if not less(lt,w[q],w[q+1]) and not less(lt,w[q+1],w[q]): w[q],w[q+1]=w[q+1],w[q]
    return tuple(w)
def promote(w,j,lt):
    # left action of tau_{n-1}...tau_j (apply tau_j first): moving element starts at 0-based position j-1, goes up
    w=list(w); n=len(w)
    for q in range(j-1,n-1):
        if not less(lt,w[q],w[q+1]) and not less(lt,w[q+1],w[q]): w[q],w[q+1]=w[q+1],w[q]
    return tuple(w)
def max_matching(Wn,adj):
    match={}
    def try_(u,seen):
        for v in adj[u]:
            if v in seen: continue
            seen.add(v)
            if v not in match or try_(match[v],seen):
                match[v]=u; return True
        return False
    cnt=0
    for u in range(Wn):
        if try_(u,set()): cnt+=1
    return cnt
def check(n,lt,stats):
    L=linexts(n,lt)
    pos={w:{v:i+1 for i,v in enumerate(w)} for w in L}
    for x in range(n):
        byA={}
        for w in L: byA.setdefault(pos[w][x],[]).append(w)
        for a in range(2,n):
            Ea=byA.get(a,[]); Em=byA.get(a-1,[]); Ep=byA.get(a+1,[])
            if not Em or not Ep: continue
            Wl=[(p_,s_) for p_ in Em for s_ in Ep]
            adj=[]
            for (pi,sg) in Wl:
                nb=set()
                for y in range(n):
                    if y==x: continue
                    i=pos[pi][y]; j=pos[sg][y]
                    if i>a-1 and j<a+1:
                        p2=demote(pi,i,lt); s2=promote(sg,j,lt)
                        assert pos.get(p2,{}).get(x)==a and pos.get(s2,{}).get(x)==a, ('not in V',lt,x,a,pi,sg,y)
                        nb.add((p2,s2))
                adj.append(list(nb))
            stats['instances']+=1
            if any(len(z)==0 for z in adj): stats['isolated']+=1
            m=max_matching(len(Wl),adj)
            if m<len(Wl):
                stats['fail']+=1
                if len(stats['ex'])<5: stats['ex'].append((n,lt,x,a,len(Wl),len(Ea)**2,m))
if __name__=='__main__':
    n=int(sys.argv[1]); a0=int(sys.argv[2]) if len(sys.argv)>2 else 0; b0=int(sys.argv[3]) if len(sys.argv)>3 else 10**9
    t=time.time(); P=posets(n)
    stats={'instances':0,'fail':0,'isolated':0,'ex':[]}
    for k,lt in enumerate(P[a0:b0]): check(n,lt,stats)
    print('n',n,'posets(labelled natural)',len(P),'range',a0,min(b0,len(P)),stats,'sec',round(time.time()-t,1))
