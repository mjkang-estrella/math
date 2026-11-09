# Faster exact decision procedure for the same orderability CSP (global adjacency relation A on pairs such that
# A restricted to every circuit C is a Hamiltonian cycle of C), with degree propagation and subcycle checks.
import itertools, sys
def orderable_fast(m, circ):
    Cs=[[i for i in range(m) if c>>i&1] for c in circ]
    pidx={}; pairs=[]
    for C in Cs:
        for a,b in itertools.combinations(C,2):
            if (a,b) not in pidx: pidx[(a,b)]=len(pairs); pairs.append((a,b))
    P=len(pairs)
    # incidence: for each circuit and each element x in C, the list of pair indices at x within C
    inc=[]  # (circuit index, element, [pair idxs])
    pair_inc=[[] for _ in range(P)]
    for ci,C in enumerate(Cs):
        for x in C:
            L=[pidx[(min(x,y),max(x,y))] for y in C if y!=x]
            k=len(inc); inc.append((ci,x,L))
            for p in L: pair_inc[p].append(k)
    pair_circ=[[] for _ in range(P)]
    for ci,C in enumerate(Cs):
        for a,b in itertools.combinations(C,2): pair_circ[pidx[(a,b)]].append(ci)
    val=[None]*P
    def subcycle_ok(ci):
        C=Cs[ci]; L=len(C); parent={x:x for x in C}; ne=0
        def f(x):
            while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
            return x
        for a,b in itertools.combinations(C,2):
            if val[pidx[(a,b)]]==1:
                ne+=1; ra,rb=f(a),f(b)
                if ra==rb and ne<L: return False
                parent[ra]=rb
        return True
    def propagate(stack, trail):
        while stack:
            p=stack.pop()
            for k in pair_inc[p]:
                ci,x,L=inc[k]
                ones=sum(1 for q in L if val[q]==1); und=[q for q in L if val[q] is None]
                if ones>2 or ones+len(und)<2: return False
                if ones==2 and und:
                    for q in und: val[q]=0; trail.append(q); stack.append(q)
                elif ones+len(und)==2 and und:
                    for q in und: val[q]=1; trail.append(q); stack.append(q)
            for ci in pair_circ[p]:
                if val[p]==1 and not subcycle_ok(ci): return False
        return True
    def rec():
        # choose undecided pair in the most constrained incidence
        best=None; bs=10**9
        for k,(ci,x,L) in enumerate(inc):
            und=[q for q in L if val[q] is None]
            if und and len(und)<bs: bs=len(und); best=und[0]
        if best is None: return all(subcycle_ok(ci) for ci in range(len(Cs)))
        for v in (1,0):
            trail=[best]; val[best]=v
            if propagate([best],trail) and rec(): return True
            for q in trail: val[q]=None
        return False
    sys.setrecursionlimit(100000)
    return rec()
