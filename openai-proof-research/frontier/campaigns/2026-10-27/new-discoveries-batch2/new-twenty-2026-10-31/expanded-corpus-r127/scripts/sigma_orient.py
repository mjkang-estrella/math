# 339418: existence of transitive sigma_n-orientations of sigma_n-k-partitions (Gyarfas? et al., arXiv:1806.00729v1, Def. 4, Conj. 2).
# Reformulation: tournament T on Z_n with s_d(b)=[b->b+d in T]; T is a transitive sigma_n-orientation of some sigma_n-k-partition
# iff T is transitive and for each d the reversal set {b: s_d(b)!=s_d(b+1)} lies in one residue class c_d mod k;
# the defining sequence is then a_d = k-1-c_d (mod k) (free if no reversal).  Bitmask backtracking over d=1..floor(n/2).
import sys, json, time, itertools
def rot(X,t,n,M):  # bit b of result = bit (b+t) of X
    t%=n
    return ((X>>t)|(X<<(n-t)))&M
def seqs(n,k,d):
    M=(1<<n)-1; out={}
    nb=n//k
    for c in range(k):
        for p in range(1<<nb):
            X=0
            for b in range(n):
                blk=((b-c-1)%n)//k
                if (p>>blk)&1: X|=1<<b
            if 2*d==n and rot(X,d,n,M)!=(~X&M): continue
            out.setdefault(X,set()).add(c)
    return out
def solve(n,k,want_all=False,timeout=100,fix=None):
    M=(1<<n)-1; m=n//2; t0=time.time()
    S=[None]*(n)
    cand={d:seqs(n,k,d) for d in range(1,m+1)}
    if fix:  # fixed defining sequence: restrict phases
        for d in range(1,m+1):
            c=(k-1-fix[d-1])%k
            cand[d]={X:cs for X,cs in cand[d].items() if (X==0 or X==M or c in cs) or (2*d==n and c in cs)}
    r=lambda d: min(d,n-d)
    checks={d:[] for d in range(1,m+1)}
    for i in range(1,n-1):
        for j in range(1,n-i):
            checks[max(r(i),r(j),r(i+j))].append((i,j))
    def get(d):
        if d<=m: return S[d]
        return (~rot(S[n-d],d,n,M))&M
    sols=[]; nodes=0
    def ok(d):
        for i,j in checks[d]:
            a=get(i); b=rot(get(j),i,n,M); c=get(i+j)
            if (a&b&~c)|(~a&~b&c)&M: return False
        return True
    def rec(d):
        nonlocal nodes
        nodes+=1
        if time.time()-t0>timeout: raise TimeoutError
        if d>m:
            sols.append(list(S[1:m+1])); return not want_all
        for X in cand[d]:
            if d==1 and fix is None and X>rot(X,1,n,M) and False: continue
            S[d]=X
            if ok(d) and rec(d+1): return True
        S[d]=None; return False
    try: rec(1); status='complete'
    except TimeoutError: status='timeout'
    return sols,status,nodes,cand
def defining(sol,n,k,cand):
    # all defining sequences compatible with the orientation
    res=[]
    for d,X in enumerate(sol,1):
        res.append(sorted({(k-1-c)%k for c in cand[d][X]}))
    return res
if __name__=='__main__':
    cmd=sys.argv[1]
    if cmd=='n6':
        n,k=6,3
        sols,st,nodes,cand=solve(n,k,want_all=True)
        defs=set()
        for s in sols:
            for t in itertools.product(*defining(s,n,k,cand)): defs.add(t)
        norm={t for t in defs if t[0]==0}
        print(json.dumps({'n':n,'k':k,'orientations':len(sols),'status':st,'defining_sequences_with_orientation':sorted(defs),'with_a1_0':sorted(norm)}))
    elif cmd=='exist':
        n,k=int(sys.argv[2]),int(sys.argv[3]); t=time.time()
        sols,st,nodes,cand=solve(n,k,timeout=float(sys.argv[4]) if len(sys.argv)>4 else 100)
        print(json.dumps({'n':n,'k':k,'found':bool(sols),'status':st,'nodes':nodes,'sec':round(time.time()-t,2),'example':[bin(x) for x in sols[0]] if sols else None,'defining':defining(sols[0],n,k,cand) if sols else None}),flush=True)
