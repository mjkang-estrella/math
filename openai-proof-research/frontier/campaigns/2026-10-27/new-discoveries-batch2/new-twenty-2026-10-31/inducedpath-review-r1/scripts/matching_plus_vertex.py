"""Reviewer's own code. Does G_{q,p} (literal source definition) contain an induced
(q-1)K_2 + K_1 ?  P_{3q-2} contains one (pairs (3i,3i+1), i<q-1, plus vertex 3q-3), so
(q-1)K_2+K_1-freeness would imply the conjecture directly (the q=3 route of
Chudnovsky-Goedgebeur-Schaudt-Zhong, arXiv:1703.05684, proves 2K_2+K_1-freeness)."""
import sys,time
q=int(sys.argv[1]); p0=int(sys.argv[2]); p1=int(sys.argv[3]); cap=float(sys.argv[4])
for p in range(p0,p1+1):
    n=q*p-2
    N=[0]*n
    for i in range(n):
        for x in [i-1,i+1]+[i+q*j-1 for j in range(1,p)]:
            x%=n
            if x!=i: N[i]|=1<<x
    full=(1<<n)-1
    found=None; t0=time.time(); nodes=0
    # vertex-transitive: fix isolated vertex = 0. Choose edges among vertices not in closed N(0).
    allowed0=full & ~(N[0]|1)
    edges=[(a,b) for a in range(n) for b in range(a+1,n) if (N[a]>>b)&1 and (allowed0>>a)&1 and (allowed0>>b)&1]
    def rec(start,allowed,chosen):
        global found,nodes
        nodes+=1
        if nodes%100000==0 and time.time()-t0>cap: raise TimeoutError
        if len(chosen)==q-1: found=list(chosen); return True
        for k in range(start,len(edges)):
            a,b=edges[k]
            if (allowed>>a)&1 and (allowed>>b)&1:
                na=allowed & ~(N[a]|N[b]|(1<<a)|(1<<b))
                chosen.append((a,b))
                if rec(k+1,na,chosen): return True
                chosen.pop()
        return False
    try:
        rec(0,allowed0,[]); st="complete"
    except TimeoutError: st="TIMEOUT"
    print(f"q={q} p={p} n={n}: status={st} induced_(q-1)K2+K1_found={found is not None} witness_isolated=0 edges={found} nodes={nodes}",flush=True)
