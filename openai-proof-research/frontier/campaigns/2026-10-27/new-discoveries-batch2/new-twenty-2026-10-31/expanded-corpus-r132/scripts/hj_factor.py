# Search for A (|A|=k) and T in Z_M with T (+) dA = Z_M (direct sum) for all d=1..k-1.
# Such (A,T) gives a colouring of [k]^(k-1): blue iff sum of iota(x_i) mod M in T (iota: letters -> A, any order).
import sys,itertools,json,time
k=int(sys.argv[1]); Mmax=int(sys.argv[2]); t0=time.time()
found=[]
for M in range(k,Mmax+1,k):
    tsize=M//k
    for A in itertools.combinations(range(1,M),k-1):
        A=(0,)+A
        dAs=[]
        ok=True
        for d in range(1,k):
            dA=sorted(set((d*a)%M for a in A))
            if len(dA)<k: ok=False;break
            dAs.append(dA)
        if not ok: continue
        # T must satisfy: for each d, T+dA tiles. Search T containing 0 (wlog), via exact cover on Z_M for d=1 then test
        # enumerate T for d=1 by backtracking
        A1=dAs[0]
        def tilings():
            cov=[False]*M; T=[]
            def rec():
                try: x=cov.index(False)
                except ValueError:
                    yield list(T); return
                for a in A1:
                    t=(x-a)%M
                    pts=[(t+b)%M for b in A1]
                    if all(not cov[p] for p in pts):
                        for p in pts: cov[p]=True
                        T.append(t); yield from rec(); T.pop()
                        for p in pts: cov[p]=False
            yield from rec()
        for T in tilings():
            good=True
            for dA in dAs[1:]:
                s=set((t+b)%M for t in T for b in dA)
                if len(s)<M: good=False;break
            if good:
                found.append((M,A,sorted(T))); break
        if found: break
        if time.time()-t0>100: break
    if found or time.time()-t0>100: break
print(json.dumps({'k':k,'Mmax':Mmax,'found':found,'secs':round(time.time()-t0,1),'lastM':M}))
