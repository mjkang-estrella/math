"""Reviewer's own code. Literal G_{q,p} from arXiv:2404.11704 main.tex l.1522:
V=[qp-3]_0, arithmetic mod n=qp-2, N(i)={i-1,i+1} u {i+qj-1 : j in [p-1]}.
Modes:
  defs q p        : symmetry of printed N(i); linear rule on [0,n-2]; Lemma A and Lemma B brute force
  lip q p [cap]   : exhaustive longest induced path (vertex-transitive: first endpoint fixed at 0)
"""
import sys, time, itertools
def build(q,p):
    n=q*p-2
    N=[set() for _ in range(n)]
    for i in range(n):
        for x in [i-1,i+1]+[i+q*j-1 for j in range(1,p)]:
            x%=n
            if x!=i: N[i].add(x)
    return n,N
def defs(q,p):
    n,N=build(q,p)
    sym=all(i in N[j] for i in range(n) for j in N[i])
    loops=any(i in N[i] for i in range(n))
    lin=True
    for i in range(n-1):
        for j in range(i+1,n-1):
            rule=(j-i==1) or ((j-i)%q==q-1)
            if rule!=(j in N[i]): lin=False
    # Lemma A: no independent set within [0,n-2] meeting all residues: search one vertex per residue
    m=n-1
    byres=[[v for v in range(m) if v%q==s] for s in range(q)]
    lemA=True; cnt=0
    def rec(s,chosen):
        nonlocal lemA,cnt
        if not lemA: return
        if s==q: lemA=False; return
        for v in byres[s]:
            if all(v not in N[u] for u in chosen):
                cnt+=1
                rec(s+1,chosen+[v])
    if q*p<=40: rec(0,[])
    else: lemA=None
    # Lemma B in edge form: two edges ab, cd in [0,n-2], same residue class pair, induced 2K2 -> impossible
    lemB=True
    if n<=40:
        E=[(a,b) for a in range(m) for b in N[a] if a<b<m]
        for (a,b),(c,d) in itertools.combinations(E,2):
            if len({a,b,c,d})<4: continue
            if {a%q,b%q}!={c%q,d%q}: continue
            if any(y in N[x] for x in (a,b) for y in (c,d)): continue
            lemB=False; break
    else: lemB=None
    print(f"defs q={q} p={p} n={n}: symmetric={sym} loops={loops} linear_rule_on_[0,n-2]={lin} "
          f"lemmaA_holds={lemA} lemmaB_holds={lemB}",flush=True)
    return sym and not loops and lin and lemA is not False and lemB is not False
def lip(q,p,cap):
    n,N=build(q,p)
    Nb=[sum(1<<x for x in N[i]) for i in range(n)]
    best=[1,None]; nodes=0; t0=time.time()
    path=[0]
    def rec(last,blocked,used):
        nonlocal nodes
        nodes+=1
        if nodes%200000==0 and time.time()-t0>cap: raise TimeoutError
        if len(path)>best[0]: best[0]=len(path); best[1]=list(path)
        cand=Nb[last]&~blocked&~used
        nb=blocked|Nb[last]|(1<<last)
        while cand:
            low=cand&-cand; w=low.bit_length()-1; cand^=low
            path.append(w)
            rec(w,nb,used|(1<<w))
            path.pop()
    try:
        rec(0,0,1)
        status="complete"
    except TimeoutError:
        status="TIMEOUT"
    # independent verification of the witness
    P=best[1]
    ok=True
    if P:
        for a in range(len(P)):
            for b in range(a+1,len(P)):
                if (P[b] in N[P[a]])!=(b==a+1): ok=False
    print(f"lip q={q} p={p} n={n}: status={status} longest_induced_path_vertices={best[0]} "
          f"conj_bound_3q-3={3*q-3} witness_verified={ok} nodes={nodes} secs={time.time()-t0:.1f} witness={P}",flush=True)
mode=sys.argv[1]
if mode=="defs":
    q=int(sys.argv[2]); ps=range(int(sys.argv[3]),int(sys.argv[4])+1)
    print("ALL_DEFS_OK" if all([defs(q,p) for p in ps]) else "DEFS_FAILURE")
else:
    q=int(sys.argv[2]); cap=float(sys.argv[5])
    for p in range(int(sys.argv[3]),int(sys.argv[4])+1): lip(q,p,cap)
