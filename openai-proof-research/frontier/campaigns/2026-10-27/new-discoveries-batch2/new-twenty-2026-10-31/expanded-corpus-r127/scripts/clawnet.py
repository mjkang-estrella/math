# 340073/340074: exhaustive generation of (claw,net)-free graphs (all, incl. disconnected) by one-vertex
# extension (class is hereditary) and e-positivity test of the chromatic symmetric function.
# Graph = tuple of adjacency bitmasks. Pure python; run via limited.py with python3 -E -P.
import sys, json, pathlib, time, itertools
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1]; OUT=D/'outputs/clawnet'
def bits(x):
    while x:
        b=x&-x; yield b.bit_length()-1; x^=b
def popc(x): return bin(x).count('1')
# ---------- forbidden induced subgraphs involving new vertex v ----------
def has_claw_with(adj,v):
    Nv=adj[v]
    # v as centre: independent 3-set in N(v)
    L=list(bits(Nv))
    for i in range(len(L)):
        a=L[i]; ra=Nv & ~adj[a] & ~((1<<(a+1))-1)
        for b in bits(ra):
            if ra & ~adj[b] & ~((1<<(b+1))-1): return True
    # v as leaf: centre c in N(v), two more neighbours x,y of c, {v,x,y} independent
    for c in L:
        cand=adj[c] & ~Nv & ~(1<<v)
        for x in bits(cand):
            if cand & ~adj[x] & ~(1<<x): return True
    return False
def has_net_with(adj,v):
    n=len(adj); Nv=adj[v]
    # v in triangle {v,a,b}; pendants pv,pa,pb pairwise nonadjacent, each adjacent to exactly its own triangle vertex
    for a in bits(Nv):
        for b in bits(Nv & adj[a]):
            if b<a: continue
            T=(1<<v)|(1<<a)|(1<<b)
            Pv=Nv & ~adj[a] & ~adj[b] & ~T
            Pa=adj[a] & ~Nv & ~adj[b] & ~T
            Pb=adj[b] & ~Nv & ~adj[a] & ~T
            for x in bits(Pv):
                for y in bits(Pa & ~adj[x]):
                    if Pb & ~adj[x] & ~adj[y]: return True
    # v as pendant attached to a, triangle {a,b,c}, v not adjacent to b,c; pendants pb,pc
    for a in bits(Nv):
        for b in bits(adj[a] & ~Nv & ~(1<<v)):
            for c in bits(adj[a] & adj[b] & ~Nv & ~(1<<v)):
                if c<b: continue
                T=(1<<a)|(1<<b)|(1<<c)
                Pb=adj[b] & ~adj[a] & ~adj[c] & ~Nv & ~T & ~(1<<v)
                Pc=adj[c] & ~adj[a] & ~adj[b] & ~Nv & ~T & ~(1<<v)
                for x in bits(Pb):
                    if Pc & ~adj[x]: return True
    return False
def is_clawnet_free_full(adj):
    n=len(adj)
    for v in range(n):
        sub=tuple(adj[u] & ((1<<(v+1))-1) for u in range(v+1))
        if has_claw_with(sub,v) or has_net_with(sub,v): return False
    return True
# ---------- isomorphism ----------
def refine(adj,col):
    n=len(adj)
    while True:
        sig=[(col[u],tuple(sorted(col[w] for w in bits(adj[u])))) for u in range(n)]
        keys=sorted(set(sig)); idx={k:i for i,k in enumerate(keys)}
        new=[idx[s] for s in sig]
        if len(keys)==len(set(col)): return new,keys
        col=new
def invariant(adj):
    n=len(adj); col,keys=refine(adj,[0]*n)
    return (n,sum(popc(a) for a in adj)//2,tuple(keys).__hash__())
def iso(A,B):
    n=len(A)
    if n!=len(B): return False
    def joint(ca,cb):
        while True:
            sa=[(ca[u],tuple(sorted(ca[w] for w in bits(A[u])))) for u in range(n)]
            sb=[(cb[u],tuple(sorted(cb[w] for w in bits(B[u])))) for u in range(n)]
            if sorted(sa)!=sorted(sb): return None
            keys=sorted(set(sa)); idx={k:i for i,k in enumerate(keys)}
            na=[idx[s] for s in sa]; nb=[idx[s] for s in sb]
            if len(keys)==len(set(ca)): return na,nb
            ca,cb=na,nb
    def rec(ca,cb):
        r=joint(ca,cb)
        if r is None: return False
        ca,cb=r
        cells={}
        for u in range(n): cells.setdefault(ca[u],[]).append(u)
        nonsing=[c for c in sorted(cells) if len(cells[c])>1]
        if not nonsing:
            m=[0]*n
            for u in range(n): m[ca[u]]=u
            mb=[0]*n
            for u in range(n): mb[cb[u]]=u
            perm={m[c]:mb[c] for c in range(n)}
            return all(((A[u]>>w)&1)==((B[perm[u]]>>perm[w])&1) for u in range(n) for w in range(n))
        c=nonsing[0]; u=cells[c][0]; K=max(ca)+1
        for w in [x for x in range(n) if cb[x]==c]:
            na=list(ca); nb=list(cb); na[u]=K; nb[w]=K
            if rec(na,nb): return True
        return False
    return rec([0]*n,[0]*n)
# ---------- chromatic symmetric function, e-expansion ----------
def partitions(n,maxp=None):
    if maxp is None: maxp=n
    if n==0: yield (); return
    for k in range(min(n,maxp),0,-1):
        for r in partitions(n-k,k): yield (k,)+r
_E={}
def e_to_m(n):
    if n in _E: return _E[n]
    P=list(partitions(n)); idx={p:i for i,p in enumerate(P)}
    # coefficient of m_lam in e_mu = number of 0-1 matrices with row sums mu, column sums lam
    def count01(mu,lam):
        lam=list(lam); from functools import lru_cache
        @lru_cache(None)
        def f(i,cols):
            if i==len(mu): return 1 if all(c==0 for c in cols) else 0
            tot=0
            for S in itertools.combinations(range(len(cols)),mu[i]):
                if all(cols[j]>0 for j in S):
                    nc=list(cols)
                    for j in S: nc[j]-=1
                    tot+=f(i+1,tuple(nc))
            return tot
        return f(0,tuple(lam))
    M=[[count01(mu,lam) for lam in P] for mu in P]
    # invert via Fractions Gaussian elimination: we need c with sum_mu c_mu M[mu][lam] = b_lam
    N=len(P); A=[[Fraction(M[i][j]) for j in range(N)] for i in range(N)]
    Inv=[[Fraction(int(i==j)) for j in range(N)] for i in range(N)]
    for col in range(N):
        piv=next(r for r in range(col,N) if A[r][col]!=0)
        A[col],A[piv]=A[piv],A[col]; Inv[col],Inv[piv]=Inv[piv],Inv[col]
        pv=A[col][col]; A[col]=[x/pv for x in A[col]]; Inv[col]=[x/pv for x in Inv[col]]
        for r in range(N):
            if r!=col and A[r][col]!=0:
                f=A[r][col]; A[r]=[x-f*y for x,y in zip(A[r],A[col])]; Inv[r]=[x-f*y for x,y in zip(Inv[r],Inv[col])]
    # b = c M  => c = b M^{-1}
    for row in Inv:
        for x in row: assert x.denominator==1
    Minv=[[int(x) for x in row] for row in Inv]
    _E[n]=(P,idx,Minv); return _E[n]
def stable_types(adj):
    n=len(adj); full=(1<<n)-1
    # independent sets containing min vertex of S, enumerated on the fly
    memo={0:{():1}}
    def F(S):
        if S in memo: return memo[S]
        v=(S&-S).bit_length()-1; rest=S & ~(1<<v) & ~adj[v]
        res={}
        # enumerate independent subsets B of rest; block = {v} U B
        stack=[(0,rest)]
        while stack:
            B,cand=stack.pop()
            sub=F(S & ~(1<<v) & ~B)
            k=popc(B)+1
            for lam,c in sub.items():
                nl=tuple(sorted(lam+(k,),reverse=True)); res[nl]=res.get(nl,0)+c
            # extend B with vertices of cand greater than max(B) to avoid duplicates
            hi=B.bit_length()
            c2=cand & ~((1<<hi)-1)
            for w in bits(c2):
                stack.append((B|(1<<w), cand & ~adj[w] & ~((1<<(w+1))-1)))
        memo[S]=res; return res
    return F(full)
def e_coeffs(adj):
    n=len(adj); P,idx,Minv=e_to_m(n)
    a=stable_types(adj); b=[0]*len(P)
    from math import factorial
    for lam,c in a.items():
        mult=1
        for k in set(lam): mult*=factorial(lam.count(k))
        b[idx[lam]]=c*mult
    return {P[j]:sum(b[i]*Minv[i][j] for i in range(len(P)) if b[i]) for j in range(len(P))}
def connected(adj):
    n=len(adj); seen=1; fr=1
    while fr:
        nf=0
        for u in bits(fr): nf|=adj[u]
        fr=nf & ~seen; seen|=nf
    return seen==(1<<n)-1
# ---------- driver ----------
def load(n):
    p=OUT/f'graphs-{n}.json'
    return [tuple(g) for g in json.loads(p.read_text())] if p.exists() else None
def gen(n):
    par=load(n-1)
    buckets={}; out=[]
    t=time.time(); cands=0
    for g in par:
        for S in range(1<<(n-1)):
            adj=list(g)+[S]
            for u in bits(S): adj[u]|=1<<(n-1)
            adj=tuple(adj); cands+=1
            if has_claw_with(adj,n-1) or has_net_with(adj,n-1): continue
            key=invariant(adj); L=buckets.setdefault(key,[])
            if any(iso(adj,h) for h in L): continue
            L.append(adj); out.append(adj)
    (OUT/f'graphs-{n}.json').write_text(json.dumps([list(g) for g in out]))
    print(json.dumps({'gen':n,'parents':len(par),'candidates':cands,'classes':len(out),'connected':sum(connected(g) for g in out),'sec':round(time.time()-t,1)}),flush=True)
if __name__=='__main__':
    cmd=sys.argv[1]
    if cmd=='selftest':
        claw=(0b1110,1,1,1)
        net=(0b000110|1<<3,0b000101|1<<4,0b000011|1<<5,1,2,4)
        print('claw free?',is_clawnet_free_full(claw),'net free?',is_clawnet_free_full(net))
        print('claw e',{k:v for k,v in e_coeffs(claw).items() if v})
        print('net e',{k:v for k,v in e_coeffs(net).items() if v})
        P4=(2,5,10,4); print('P4 e',{k:v for k,v in e_coeffs(P4).items() if v})
        C4=(0b1010,0b0101,0b1010,0b0101); print('C4 e',{k:v for k,v in e_coeffs(C4).items() if v})
    elif cmd=='init':
        (OUT/'graphs-1.json').write_text(json.dumps([[0]]))
    elif cmd=='gen':
        for n in range(int(sys.argv[2]),int(sys.argv[3])+1): gen(n)
    elif cmd=='epos':
        n=int(sys.argv[2]); a=int(sys.argv[3]); b=int(sys.argv[4]); G=load(n)[a:b]
        bad=[]; t=time.time(); done=0
        for j,g in enumerate(G):
            if not connected(g): done+=1; continue
            c=e_coeffs(g); neg={str(k):v for k,v in c.items() if v<0}
            if neg: bad.append({'index':a+j,'adj':list(g),'negative':neg})
            done+=1
            if time.time()-t>100: break
        rec={'n':n,'start':a,'end':a+done,'requested_end':b,'bad':bad,'sec':round(time.time()-t,1)}
        with (OUT/f'epos-{n}.jsonl').open('a') as f: f.write(json.dumps(rec)+'\n')
        print(json.dumps(rec),flush=True)
def genchunk(n,a,b):
    par=load(n-1)[a:b]; buckets={}; out=[]; t=time.time(); cands=0
    for g in par:
        for S in range(1<<(n-1)):
            adj=list(g)+[S]
            for u in bits(S): adj[u]|=1<<(n-1)
            adj=tuple(adj); cands+=1
            if has_claw_with(adj,n-1) or has_net_with(adj,n-1): continue
            key=invariant(adj); L=buckets.setdefault(key,[])
            if any(iso(adj,h) for h in L): continue
            L.append(adj); out.append(adj)
    (OUT/f'part-{n}-{a:06d}-{b:06d}.json').write_text(json.dumps([list(g) for g in out]))
    print(json.dumps({'genchunk':n,'parents':[a,b],'candidates':cands,'classes_in_chunk':len(out),'sec':round(time.time()-t,1)}),flush=True)
def merge(n):
    parts=sorted(OUT.glob(f'part-{n}-*.json')); buckets={}; out=[]; t=time.time(); total=0
    for p in parts:
        for g in json.loads(p.read_text()):
            g=tuple(g); total+=1
            key=invariant(g); L=buckets.setdefault(key,[])
            if any(iso(g,h) for h in L): continue
            L.append(g); out.append(g)
    (OUT/f'graphs-{n}.json').write_text(json.dumps([list(g) for g in out]))
    print(json.dumps({'merge':n,'parts':[p.name for p in parts],'entries':total,'classes':len(out),'connected':sum(connected(g) for g in out),'sec':round(time.time()-t,1)}),flush=True)
if __name__=='__main__' and sys.argv[1]=='genchunk': genchunk(int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]))
if __name__=='__main__' and sys.argv[1]=='merge': merge(int(sys.argv[2]))
