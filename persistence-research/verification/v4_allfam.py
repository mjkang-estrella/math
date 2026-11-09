import sys, time
sys.setrecursionlimit(100000)
from v3_v2fam import v2
def gen(n, maxd=9):
    if n==1: yield (); return
    for d in range(min(maxd,9),1,-1):
        if n%d==0:
            for rest in gen(n//d, d): yield (d,)+rest
def supv2(nu, cap):
    digs=sorted(set(nu)); rem0=tuple(nu.count(d) for d in digs)
    best=[-1]; nodes=[0]
    def dfs(k,t,rem):
        nodes[0]+=1
        if nodes[0]>cap: raise OverflowError
        full = sum(rem)==0
        val = k+v2(t) if full else k
        if val>best[0]: best[0]=val
        p5=5**k
        if t&1: dfs(k+1,(p5+t)>>1,rem)
        for i,d in enumerate(digs):
            if rem[i] and (d&1)==(t&1):
                r=list(rem); r[i]-=1; dfs(k+1,(d*p5+t)>>1,tuple(r))
    dfs(0,0,rem0); return best[0],nodes[0]
for t in (2**19*3**4*7**6, 2**4*3**20*7**5):
    fams=list(gen(t)); res=[]; capped=[]
    t0=time.time()
    for nu in fams:
        try: res.append((supv2(list(nu),int(sys.argv[1]))[0],''.join(map(str,sorted(nu)))))
        except OverflowError: capped.append(''.join(map(str,sorted(nu))))
    res.sort(reverse=True)
    print(f"target {t}: {len(fams)} families, decided {len(res)}, capped {len(capped)}, {time.time()-t0:.0f}s")
    print("  top sup v2:", res[:5])
    print("  min-length family:", [r for r in res if len(r[1])==min(len(x[1]) for x in res)][:3])
    if capped: print("  capped examples:", capped[:3])
