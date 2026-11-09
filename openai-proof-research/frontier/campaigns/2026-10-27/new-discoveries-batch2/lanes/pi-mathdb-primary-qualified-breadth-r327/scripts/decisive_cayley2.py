import itertools,math,json
_rt={}
def ranktype(t):
    r=_rt.get(t)
    if r is None:
        s=sorted(set(t)); m={v:i+1 for i,v in enumerate(s)}
        r=tuple(m[v] for v in t); _rt[t]=r
    return r
def contains(w,p):
    L=len(p)
    for combo in itertools.combinations(range(len(w)),L):
        if ranktype(tuple(w[i] for i in combo))==p: return True
    return False
def surj_words(n):
    for k in range(1,n+1):
        for w in itertools.product(range(1,k+1),repeat=n):
            if len(set(w))==k: yield w
def main():
    L=5; N=8   # patterns length<=5, sizes n<=8 (Fubini(8)=545835 words; heavier)
    pats=[]
    for l in range(1,L+1):
        for k in range(1,l+1):
            for w in itertools.product(range(1,k+1),repeat=l):
                if len(set(w))==k: pats.append(w)
    pidx={p:i for i,p in enumerate(pats)}
    avoid=[[0]*len(pats) for _ in range(N+1)]
    for n in range(1,N+1):
        cnt=[0]*len(pats)
        for w in surj_words(n):
            ts=set()
            for l in range(1,min(n,L)+1):
                for combo in itertools.combinations(range(n),l):
                    ts.add(ranktype(tuple(w[i] for i in combo)))
            for p in pats:
                if len(p)<=n and p not in ts: cnt[pidx[p]]+=1
        avoid[n]=cnt
        print("n=",n,"done",flush=True)
    viol=[];pairs=0
    for i,p in enumerate(pats):
        for j,q in enumerate(pats):
            if len(p)==len(q) and max(p)<=max(q):
                pairs+=1
                bad=[n for n in range(1,N+1) if avoid[n][i]<avoid[n][j]]
                if bad:
                    viol.append({"p":''.join(map(str,p)),"q":''.join(map(str,q)),
                        "max_p":max(p),"max_q":max(q),"n":bad[0],
                        "cay_n_p":avoid[bad[0]][i],"cay_n_q":avoid[bad[0]][j]})
    res={"scope":f"same-length patterns length<={L}, sizes n<={N}","checked_pairs":pairs,
         "num_violations":len(viol),"violations":viol[:60]}
    json.dump(res,open("work/decisive-cayley-sweep.json","w"),indent=1)
    print("pairs:",pairs,"violations:",len(viol))
    if viol: print(json.dumps(viol[:10],indent=1))
if __name__=="__main__": main()
