# Iterated local search for maximum independent set (ARW-style (1,2)-swaps + random perturbation).
import random,time
def ils(adj,N,seconds,seed,start=None):
    rnd=random.Random(seed); t0=time.time()
    A=set(start) if start else set()
    tight=[0]*N  # number of solution neighbours
    nbl=[[j for j in range(N) if adj[i]>>j&1] for i in range(N)]
    def add(v):
        A.add(v)
        for u in nbl[v]: tight[u]+=1
    def rem(v):
        A.discard(v)
        for u in nbl[v]: tight[u]-=1
    for v in list(A): A.discard(v); add(v)
    def free_vertices(): return [v for v in range(N) if v not in A and tight[v]==0]
    def fill():
        f=free_vertices(); rnd.shuffle(f)
        for v in f:
            if tight[v]==0 and v not in A: add(v)
    fill(); best=set(A); it=0
    while time.time()-t0<seconds:
        it+=1
        improved=True
        while improved:
            improved=False
            cand=list(A); rnd.shuffle(cand)
            for x in cand:
                # 1-tight neighbours of x
                L=[u for u in nbl[x] if tight[u]==1 and u not in A]
                if len(L)<2: continue
                rnd.shuffle(L)
                found=False
                for i in range(len(L)):
                    for j in range(i+1,len(L)):
                        if not adj[L[i]]>>L[j]&1:
                            rem(x); add(L[i]); add(L[j]); fill(); improved=True; found=True; break
                    if found: break
                if found: break
        if len(A)>len(best): best=set(A)
        # perturb: force in k random non-solution vertices
        k=1 if rnd.random()<0.5 else 2
        if len(A)<len(best)-2: A_=set(best); [rem(v) for v in list(A)]; [add(v) for v in A_]
        for _ in range(k):
            v=rnd.randrange(N)
            if v in A: continue
            for u in nbl[v]:
                if u in A: rem(u)
            add(v)
        fill()
    return best,it
