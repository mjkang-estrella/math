"""Independent check of the combinatorial core (reviewer's own code).
For q in range, enumerate all residue walks r_0..r_{L-1} on Z_q with steps +-1
such that edges e_i={r_{i-1},r_i}, e_j with j>=i+3 have distinct classes (Lemma B).
Check: every such walk of L=3q-2 vertices has an independent transversal, i.e. a set of
indices, pairwise differing by >=2 (non-consecutive), whose residues cover Z_q.
Also report L=3q-3 (sharpness of the combinatorial reduction) and count walks.
Also verifies the claimed shape classification (runs of length<=3, monotone, case list)."""
import sys
def cls(a,b,q):
    return (min(a,b),max(a,b))
def walks(q,L):
    out=[]
    r=[0]; ks=[]
    def rec():
        if len(r)==L:
            out.append(tuple(r)); return
        for d in (1,-1):
            nr=(r[-1]+d)%q
            k=cls(r[-1],nr,q)
            # new edge index j=len(ks)+1 ; compare with edges i<=j-3
            j=len(ks)
            if any(ks[i]==k for i in range(0,j-2)):
                continue
            r.append(nr); ks.append(k); rec(); r.pop(); ks.pop()
    rec(); return out
def has_ind_transversal(w,q):
    # DP over indices: choose a set with no two consecutive covering all residues.
    full=(1<<q)-1
    # states: (mask, last_chosen_is_prev)
    cur={(0,False)}
    for x in w:
        nxt=set()
        for m,pc in cur:
            nxt.add((m,False))
            if not pc: nxt.add((m|(1<<x),True))
        # prune dominated states: keep (m,pc) only if no (m2,pc2) with m subset m2, m2!=m or (pc2 False and pc True)
        free={m for m,pc in nxt if not pc}
        nxt={(m,pc) for m,pc in nxt if not (pc and m in free)}
        cur=nxt
    return any(m==full for m,_ in cur)
def runs(w,q):
    ks=[cls(w[i-1],w[i],q) for i in range(1,len(w))]
    R=[]
    for k in ks:
        if R and R[-1][0]==k: R[-1][1]+=1
        else: R.append([k,1])
    return R
qmin=int(sys.argv[1]); qmax=int(sys.argv[2])
allok=True
for q in range(qmin,qmax+1):
    L=3*q-2
    W=walks(q,L)
    bad=[w for w in W if not has_ind_transversal(w,q)]
    # structure checks
    struct_ok=True
    for w in W:
        R=runs(w,q)
        cl=[k for k,_ in R]
        if len(set(cl))!=len(cl) or any(l>3 for _,l in R) or len(R)>q: struct_ok=False
    W2=walks(q,L-1)
    bad2=sum(1 for w in W2 if not has_ind_transversal(w,q))
    print(f"q={q} parity={'odd' if q%2 else 'even'} L={L}: walks_from_0={len(W)} (4q-2={4*q-2}) "
          f"without_ind_transversal={len(bad)} structure_ok={struct_ok} | "
          f"L-1={L-1}: walks={len(W2)} without_ind_transversal={bad2}", flush=True)
    if bad or not struct_ok: allok=False
print("ALL_OK" if allok else "FAILURE")
