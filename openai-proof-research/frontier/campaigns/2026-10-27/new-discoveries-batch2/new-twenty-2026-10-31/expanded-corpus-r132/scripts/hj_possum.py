# Position-dependent additive colourings: blue iff sum_i iota_i(x_i) in T (G abelian given as Z_m1 x ... ).
# Valid (sufficient condition) if T (+) A_S = G for every nonempty S subset [n], A_S = {sum_{i in S} iota_i(j): j in [k]}.
import sys,itertools,json,time
def run(k,mods,Tsize,limit):
    n=k-1; G=list(itertools.product(*[range(m) for m in mods])); N=len(G)
    add=lambda a,b: tuple((x+y)%m for x,y,m in zip(a,b,mods))
    zero=tuple(0 for _ in mods)
    t0=time.time(); res=None
    # candidate T: contain zero
    def is_factor(T,A):
        s=set(add(t,a) for t in T for a in A)
        return len(s)==N and len(A)==len(set(A))
    Ts=[ (zero,)+c for c in itertools.combinations([g for g in G if g!=zero],Tsize-1)]
    for T in Ts:
        # iota_i: tuples of k elements of G, wlog iota_i(0)=zero? (translation changes c only) yes wlog
        cands=[ (zero,)+c for c in itertools.permutations([g for g in G if g!=zero],k-1)]
        cands=[c for c in cands if is_factor(T,c)]
        # subset sums: maintain list of A_S for subsets of chosen positions
        chosen=[]
        def rec(sums):
            nonlocal res
            if time.time()-t0>limit: return True
            if len(chosen)==n:
                res=(T,list(chosen)); return True
            for c in cands:
                if chosen and c<chosen[-1]: continue  # symmetric order wlog
                new=[tuple(add(a,b) for a,b in zip(s,c)) for s in sums]
                if all(is_factor(T,A) for A in new):
                    chosen.append(c)
                    if rec(sums+new+[c]): return True
                    chosen.pop()
            return False
        if rec([]): break
    return dict(k=k,mods=mods,Tsize=Tsize,found=res is not None and len(res[1])==n,res=res,secs=round(time.time()-t0,1))
if __name__=='__main__':
    k=int(sys.argv[1]); mods=tuple(int(x) for x in sys.argv[2].split(',')); Ts=int(sys.argv[3]); lim=float(sys.argv[4])
    print(json.dumps(run(k,mods,Ts,lim)))
