# Search for counterexamples to Crenshaw--Oxley Conjecture 4 (arXiv 2203.08305): a 3-connected orderable binary
# matroid is graphic.  Definitions (source Section 1): an ordering of M assigns a cyclic order to each circuit; it is
# consistent if whenever e,f lie in circuits C,C' and are adjacent in the order of C, they are adjacent in that of C'.
# Equivalent CSP used here: a global set A of "adjacent" pairs such that for every circuit C, the graph (C, A|C) is a
# single Hamiltonian cycle on C (|C|>=3 in a simple matroid).  [Given a consistent ordering, A = pairs adjacent in some
# circuit; conversely the cycles A|C give the orderings.]
# Facts used for pruning (source): Prop 8(i) orderability is closed under deletion, so the orderable simple binary
# matroids of rank r containing a fixed basis form a down-closed family over the remaining points of PG(r-1,2);
# Prop 9: orderable binary with a spanning circuit => graphic; a spanning circuit persists in supersets of full rank,
# so such branches contain no counterexample and are pruned.  Counterexamples must be 3-connected and non-graphic.
import sys, itertools, json, time
r=int(sys.argv[1]); MAXM=int(sys.argv[2]); BUDGET=float(sys.argv[3])
pts=list(range(1,1<<r)); basis=[1<<i for i in range(r)]; others=[p for p in pts if p not in basis]
def rank(vecs):
    rows=[];
    for v in vecs:
        for b in rows:
            v=min(v,v^b)
        if v: rows.append(v)
    return len(rows)
def circuits(vecs):
    m=len(vecs)
    # cycle space: subsets summing to zero; enumerate via kernel basis
    # build kernel basis by Gaussian elimination tracking combinations
    piv={}; ker=[]
    for i,v in enumerate(vecs):
        comb=1<<i; x=v
        for p in sorted(piv,reverse=True):
            if x>>p&1: x^=piv[p][0]; comb^=piv[p][1]
        if x: piv[x.bit_length()-1]=(x,comb)
        else: ker.append(comb)
    sup=set()
    for mask in range(1,1<<len(ker)):
        s=0
        for j in range(len(ker)):
            if mask>>j&1: s^=ker[j]
        sup.add(s)
    sup=sorted(sup,key=lambda s:bin(s).count('1'))
    circ=[]
    for s in sup:
        if not any((c&s)==c for c in circ): circ.append(s)
    return circ
def orderable(m,circ):
    # variables: pair (i,j) -> 0/1/None ; constraint per circuit: A|C is a Hamiltonian cycle
    pairs={}
    Cs=[[i for i in range(m) if c>>i&1] for c in circ]
    val={}
    pair_circ={}
    for ci,C in enumerate(Cs):
        for a,b in itertools.combinations(C,2): pair_circ.setdefault((a,b),[]).append(ci)
    def check(ci):
        C=Cs[ci]; L=len(C)
        deg={x:0 for x in C}; und={x:0 for x in C}; edges=[]
        for a,b in itertools.combinations(C,2):
            v=val.get((a,b))
            if v==1: deg[a]+=1; deg[b]+=1; edges.append((a,b))
            elif v is None: und[a]+=1; und[b]+=1
        for x in C:
            if deg[x]>2 or deg[x]+und[x]<2: return False
        # no premature subcycle among decided edges
        parent={x:x for x in C}
        def find(x):
            while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
            return x
        for a,b in edges:
            ra,rb=find(a),find(b)
            if ra==rb and len(edges)<L: return False
            parent[ra]=rb
        if len(edges)==L and len({find(x) for x in C})!=1: return False
        return True
    allpairs=sorted(pair_circ,key=lambda p:-len(pair_circ[p]))
    def rec(i):
        if i==len(allpairs): return True
        p=allpairs[i]
        for v in (1,0):
            val[p]=v
            if all(check(ci) for ci in pair_circ[p]) and rec(i+1): return True
            del val[p]
        return False
    sys.setrecursionlimit(100000)
    return rec(0)
def has_spanning_circuit(circ,rk):
    return any(bin(c).count('1')==rk+1 for c in circ)
def connectivity3(vecs):
    m=len(vecs); rk=rank(vecs)
    for k in (1,2):
        for X in itertools.combinations(range(m),k):
            pass
    # lambda(X)=r(X)+r(E-X)-r(M); 3-connected iff no X with |X|,|E-X|>=k and lambda<k for k=1,2
    for size in range(1,m//2+1):
        for X in itertools.combinations(range(m),size):
            Y=[vecs[i] for i in range(m) if i not in X]
            lam=rank([vecs[i] for i in X])+rank(Y)-rk
            if lam<1 and size>=1: return False
            if lam<2 and size>=2: return False
    return True
t=time.time(); nodes=0; stats={'orderable_nodes':0,'pruned_nonorderable':0,'pruned_spanning_circuit':0}
cands=[]; done=True
def dfs(cur,start):
    global nodes,done
    if time.time()-t>BUDGET: done=False; return
    nodes+=1
    vecs=basis+cur
    for idx in range(start,len(others)):
        if len(vecs)+1>MAXM: break
        nv=vecs+[others[idx]]
        circ=circuits(nv)
        if has_spanning_circuit(circ,r): stats['pruned_spanning_circuit']+=1; continue
        if not orderable(len(nv),circ): stats['pruned_nonorderable']+=1; continue
        stats['orderable_nodes']+=1
        cosimple=all(not any(bin(c).count('1')==2 for c in circuits_dual) for circuits_dual in [[]])
        if len(nv)>=r+3 and connectivity3(nv): cands.append(nv)
        dfs(cur+[others[idx]],idx+1)
dfs([],0)
print(json.dumps({'rank':r,'max_elements':MAXM,'complete':done,'nodes':nodes,**stats,'num_3connected_orderable_without_spanning_circuit':len(cands),'examples':cands[:5],'secs':round(time.time()-t,1)}))
