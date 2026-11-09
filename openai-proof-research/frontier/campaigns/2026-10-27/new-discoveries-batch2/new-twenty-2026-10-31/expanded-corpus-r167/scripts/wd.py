# 363761 (Kuenzel? / arXiv:2407.01121 Conjecture 2.1): well-dominated (WD) graphs G that are not trivially WD;
# test whether G (x) H is non-WD for H in a fixed test family (certified by two minimal dominating sets of different sizes).
import sys,json,random,time,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from g6 import parse
def nbh(n,adj): return [adj[v]|(1<<v) for v in range(n)]
def wellcovered(n,adj):
    sizes=set()
    def rec(cand,cur,size,excl):
        # enumerate maximal independent sets: cand = available vertices
        if cand==0:
            if excl==0: sizes.add(size)
            return
        if len(sizes)>1: return
        v=(cand&-cand).bit_length()-1
        rec(cand&~adj[v]&~(1<<v),cur|(1<<v),size+1,excl&~adj[v]&~(1<<v))
        rec(cand&~(1<<v),cur,size,excl|(1<<v) if True else excl)
    # standard: maximal iff no excluded vertex can be added; track excl as vertices skipped that are not dominated
    sizes.clear()
    def rec2(i,I,blocked):
        if i==n:
            # maximal check
            for v in range(n):
                if not (I>>v)&1 and not (adj[v]&I): return
            sizes.add(bin(I).count('1')); return
        if len(sizes)>1: return
        if not (blocked>>i)&1: rec2(i+1,I|(1<<i),blocked|adj[i])
        rec2(i+1,I,blocked)
    rec2(0,0,0)
    return len(sizes)==1
def mds_sizes(n,N):
    full=(1<<n)-1; sizes=set()
    for D in range(1,1<<n):
        u=0; m=D
        while m:
            v=(m&-m).bit_length()-1; m&=m-1; u|=N[v]
        if u!=full: continue
        ok=True; m=D
        while m and ok:
            v=(m&-m).bit_length()-1; m&=m-1
            u2=0; m2=D&~(1<<v)
            while m2:
                w=(m2&-m2).bit_length()-1; m2&=m2-1; u2|=N[w]
            if u2==full: ok=False
        if ok: sizes.add(bin(D).count('1'))
    return sizes
def trivially(n,adj,N):
    simp=[v for v in range(n) if all(((adj[x]|(1<<x))&N[v])==N[v] for x in range(n) if (N[v]>>x)&1)]
    full=(1<<n)-1
    def rec(cov):
        if cov==full: return True
        v=((~cov)&-(~cov)).bit_length()-1  # lowest uncovered
        for s in simp:
            if (N[s]>>v)&1 and not (N[s]&cov):
                if rec(cov|N[s]): return True
        return False
    return rec(0)
def strong(nA,NA,nB,NB):
    n=nA*nB; N=[0]*n
    for a in range(nA):
        for b in range(nB):
            m=0
            for a2 in range(nA):
                if (NA[a]>>a2)&1:
                    for b2 in range(nB):
                        if (NB[b]>>b2)&1: m|=1<<(a2*nB+b2)
            N[a*nB+b]=m
    return n,N
def random_mds(n,N,rng):
    full=(1<<n)-1; order=list(range(n)); rng.shuffle(order); D=full
    cnt=[bin(N[v]&D).count('1') for v in range(n)]  # number of D-vertices dominating v
    # remove vertices while remains dominating
    for v in order:
        # can remove v iff every w in N[v] has another dominator in D
        m=N[v]; ok=True
        while m:
            w=(m&-m).bit_length()-1; m&=m-1
            if bin(N[w]&D).count('1')<=1: ok=False; break
        if ok: D&=~(1<<v)
    return D
def nonwd_cert(n,N,trials,rng):
    seen={}
    for _ in range(trials):
        D=random_mds(n,N,rng); s=bin(D).count('1')
        if s not in seen: seen[s]=D
        if len(seen)>1: return seen
    return None
def cyc(k):
    return k,[((1<<((v+1)%k))|(1<<((v-1)%k))) for v in range(k)]
if __name__=='__main__':
    files=sys.argv[1:-1]; trials=int(sys.argv[-1]); rng=random.Random(12345); t0=time.time()
    tests={'C4':cyc(4),'C5':cyc(5)}
    tests={k:(n,nbh(n,a)) for k,(n,a) in tests.items()}
    res={'wd':0,'nontrivial_wd':0,'fails':[],'byH':{}}
    nontriv=[]
    for f in files:
        for line in open(f):
            n,adj=parse(line)
            if not wellcovered(n,adj): continue
            N=nbh(n,adj)
            if len(mds_sizes(n,N))!=1: continue
            res['wd']+=1
            if trivially(n,adj,N): continue
            res['nontrivial_wd']+=1; nontriv.append(line.strip())
            found=None
            for hn,(nb,NB) in tests.items():
                nP,NP=strong(n,N,nb,NB)
                c=nonwd_cert(nP,NP,trials,rng)
                if c: found=(hn,{s:bin(D).count('1') for s,D in c.items()}); break
            if found: res['byH'][found[0]]=res['byH'].get(found[0],0)+1
            else: res['fails'].append(line.strip())
    res['secs']=round(time.time()-t0,1); res['nontrivial_list']=nontriv[:200]
    print(json.dumps(res))
