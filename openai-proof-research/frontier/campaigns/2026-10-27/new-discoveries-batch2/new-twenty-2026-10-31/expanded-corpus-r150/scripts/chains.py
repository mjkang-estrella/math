# Exhaustive check of Conjecture 4.1 (Griggs, full lattice) / 4.2 (Tomon, upper half) of arXiv:1911.09533
# for small n: for every dominated sequence s, search for a chain decomposition with sizes s.
import sys, itertools, json, time
from math import comb
mode=sys.argv[1]; n=int(sys.argv[2]); limit=float(sys.argv[3]) if len(sys.argv)>3 else 100
pc=lambda x: bin(x).count('1')
m=n//2; M=comb(n,m)
# symmetric chain sizes
sig=[]
for k in range(m+1):
    cnt=comb(n,k)-(comb(n,k-1) if k>0 else 0)
    sig+= [n-2*k+1]*cnt
sig.sort(reverse=True); assert len(sig)==M
if mode=='full':
    elems=list(range(1<<n)); target_sig=sig; mid=[x for x in elems if pc(x)==m]
else:
    lo=(n+1)//2
    elems=[x for x in range(1<<n) if pc(x)>=lo]; target_sig=[(t+1)//2 for t in sig]; mid=[x for x in elems if pc(x)==lo]
    assert len(mid)==M
total=len(elems); assert sum(target_sig)==total
comp=lambda a,b: (a&b)==a or (a&b)==b
others=[x for x in elems if x not in set(mid)]
# order: far from middle level first
mlev=pc(mid[0])
import random
ORDER=sys.argv[4] if len(sys.argv)>4 else 'far'
REPS=int(sys.argv[5]) if len(sys.argv)>5 else 1
CH=int(sys.argv[6]) if len(sys.argv)>6 else 1; CI=int(sys.argv[7]) if len(sys.argv)>7 else 0
others.sort(key=lambda x:((-1 if ORDER=='far' else 1)*abs(pc(x)-mlev), x))
cand={x:[i for i,b in enumerate(mid) if comp(x,b)] for x in others}
def dominated_seqs():
    pre=list(itertools.accumulate(target_sig))
    res=[]
    def rec(i,prev,acc,seq):
        rem=M-i
        if i==M:
            if acc==total: res.append(tuple(seq))
            return
        # remaining parts each >=1 and <=prev
        for v in range(min(prev,total-acc-(rem-1)),0,-1):
            if acc+v>pre[i]: continue
            if acc+v+ v*(rem-1) < total: break
            seq.append(v); rec(i+1,v,acc+v,seq); seq.pop()
    rec(0,target_sig[0],0,[])
    return res
def solve(s,deadline,seed=None):
    if seed is not None:
        rnd=random.Random(seed)
        for x in cand: rnd.shuffle(cand[x])
    s=sorted(s,reverse=True)
    chains=[[b] for b in mid]; cnt=[1]*M
    nodes=[0]
    def feasible():
        c=sorted(cnt,reverse=True)
        return all(c[i]<=s[i] for i in range(M))
    def rec(k):
        nodes[0]+=1
        if nodes[0]%20000==0 and time.monotonic()>deadline: raise TimeoutError
        if k==len(others):
            return sorted(cnt,reverse=True)==s
        x=others[k]; tried=set()
        for i in cand[x]:
            ch=chains[i]
            key=(cnt[i],)  # chains with identical state are not interchangeable in general; no symmetry cut
            if all(comp(x,y) for y in ch):
                cnt[i]+=1
                if feasible():
                    ch.append(x)
                    if rec(k+1): return True
                    ch.pop()
                cnt[i]-=1
        return False
    ok=rec(0)
    return ok,nodes[0],[sorted(c) for c in chains] if ok else None
seqs=dominated_seqs()
print('mode',mode,'n',n,'M',M,'sigma',target_sig,'num_dominated',len(seqs),flush=True)
t0=time.monotonic(); bad=[]; unk=[]; maxnodes=0
for si,s in enumerate(seqs):
    if si%CH!=CI: continue
    try:
        ok=False
        for rep in range(REPS):
            try:
                ok,nodes,ch=solve(s,time.monotonic()+limit,seed=(None if rep==0 else rep))
                if ok: break
            except TimeoutError:
                if rep==REPS-1: raise
        maxnodes=max(maxnodes,nodes)
        maxnodes=max(maxnodes,nodes)
        if not ok: bad.append(s); print('NO DECOMPOSITION',s,flush=True)
    except TimeoutError:
        unk.append(s); print('TIMEOUT',s,flush=True)
print('done',len(seqs),'bad',len(bad),'unknown',len(unk),'maxnodes',maxnodes,'secs',round(time.monotonic()-t0,2))
