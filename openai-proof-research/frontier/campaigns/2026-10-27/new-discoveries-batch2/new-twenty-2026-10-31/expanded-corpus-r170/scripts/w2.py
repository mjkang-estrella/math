# Search connected graphs: not well-covered but condition (2) holds  (=> counterexample to 358956 Conjecture).
# Also report W2-vs-(2) mismatches directly using W2 <=> (no isolated, not P3, G-v well-covered for all v) [source Thm w2shed].
import sys,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp_sweep_lib import parse
def maximal_indeps(n,nb):
    # Bron-Kerbosch on complement graph: maximal independent sets of G restricted to vertex mask U
    out=[]
    def bk(R,P,X):
        if P==0 and X==0: out.append(R); return
        # pivot
        u=(P|X)&-(P|X); u=u.bit_length()-1
        cand=P&nb[u] | (P & (1<<u))
        # vertices not adjacent-in-complement to u: in complement, nbrs of u are non-neighbors in G; standard BK on complement picks P \ Ncomp(u) = P & (N_G(u) | {u})
        c=cand
        while c:
            lb=c&-c; v=lb.bit_length()-1; c^=lb
            nv=~nb[v] & ~(1<<v)  # complement neighbours
            bk(R|lb,P&nv,X&nv); P&=~lb; X|=lb
    return bk,out
def mis_list(n,nb,U):
    bk,out=maximal_indeps(n,nb); bk(0,U,0); return out
def pc(x): return bin(x).count('1')
def cond2(n,nb,Ms):
    for M in Ms:
        x=M
        while x:
            lb=x&-x; v=lb.bit_length()-1; x^=lb
            rest=M&~lb
            P=0; y=nb[v]
            while y:
                l2=y&-y; u=l2.bit_length()-1; y^=l2
                if nb[u]&rest==0: P|=l2
            if P==0: return False
            # clique check
            z=P
            while z:
                l3=z&-z; u=l3.bit_length()-1; z^=l3
                if (P&~l3)&~nb[u]: return False
    return True
def wc(n,nb,U):
    Ms=mis_list(n,nb,U); s={pc(M) for M in Ms}; return len(s)<=1,Ms
def w2(n,nb):
    full=(1<<n)-1
    if any(nb[v]==0 for v in range(n)): return False
    if n==3 and sorted(pc(x) for x in nb)==[1,1,2]: return False
    for v in range(n):
        ok,_=wc(n,nb,full&~(1<<v))
        if not ok: return False
    return True
if __name__=='__main__':
    n=int(sys.argv[1]);start=int(sys.argv[2]);cnt=int(sys.argv[3])
    lines=open(f'sources/graphdata/graph{n}c.g6').read().split()
    t=time.time(); stats=dict(tested=0,notwc=0,c2=0,w2=0,mismatch=0)
    for idx in range(start,min(len(lines),start+cnt)):
        adj=parse(lines[idx]); nb=[sum(1<<w for w in a) for a in adj]
        stats['tested']+=1
        iswc,Ms=wc(n,nb,(1<<n)-1)
        c2=cond2(n,nb,Ms)
        if c2: stats['c2']+=1
        if not iswc: stats['notwc']+=1
        W=w2(n,nb) if iswc else False
        if W: stats['w2']+=1
        if W!=c2: stats['mismatch']+=1; print('MISMATCH',idx,lines[idx],'wc',iswc,'w2',W,'c2',c2,flush=True)
    print(n,start,start+cnt,len(lines),stats,round(time.time()-t,1))
