import itertools,math,json
from collections import defaultdict

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
    res={"validations":[],"violations":[],"scope":"patterns length<=5, n<=7, exact enumeration of surjective words"}
    WC={}
    # Validation A: |Cay_n(112)| and |Cay_n(122)| = (n+1)!/2  (source Cor 6.8 + equivalence)
    for p in [(1,1,2),(1,2,2)]:
        det=[(n,sum(1 for w in surj_words(n) if not contains(w,p))) for n in range(2,7)]
        res["validations"].append({"check":"|Cay_n(%s)|=(n+1)!/2"%''.join(map(str,p)),
                                   "ok":all(v==math.factorial(n+1)//2 for (n,v),(_,e) in zip(det,[(x,math.factorial(x+1)//2) for x,_ in det])),
                                   "detail":det})
    # Validation B: source claim |Cay_n(13442)|=|Cay_n(14233)| for n<=9 (we check n<=7)
    det=[]
    for n in range(1,8):
        a=sum(1 for w in surj_words(n) if not contains(w,(1,3,4,4,2)))
        b=sum(1 for w in surj_words(n) if not contains(w,(1,4,2,3,3)))
        det.append({"n":n,"a":a,"b":b,"equal":a==b})
    res["validations"].append({"check":"13442 vs 14233 equal counts n<=7","detail":det})

    # Sweep: all patterns length<=5; |Cay_n(p)| for n=1..7 via type-set per word
    L=5
    pats=[]
    for l in range(1,L+1):
        for k in range(1,l+1):
            for w in itertools.product(range(1,k+1),repeat=l):
                if len(set(w))==k: pats.append(w)
    pidx={p:i for i,p in enumerate(pats)}
    avoid=[[0]*len(pats) for _ in range(8)]  # avoid[n][p]
    for n in range(1,8):
        cnt=[0]*len(pats)
        for w in surj_words(n):
            ts=set()
            for l in range(1,min(n,L)+1):
                for combo in itertools.combinations(range(n),l):
                    ts.add(ranktype(tuple(w[i] for i in combo)))
            base=0
            for p in pats:
                if len(p)<=n and p not in ts: cnt[pidx[p]]+=1
        avoid[n]=cnt
    # check conjecture 8.8: max(p)<=max(q) => avoid[n][p] >= avoid[n][q] for all n<=7
    viol=[]
    pairs=0
    for i,p in enumerate(pats):
        for j,q in enumerate(pats):
            if max(p)<=max(q):
                pairs+=1
                bad=[n for n in range(1,8) if avoid[n][i]<avoid[n][j]]
                if bad:
                    viol.append({"p":''.join(map(str,p)),"q":''.join(map(str,q)),
                                 "max_p":max(p),"max_q":max(q),"n":bad[0],
                                 "cay_n_p":avoid[bad[0]][i],"cay_n_q":avoid[bad[0]][j]})
    res["violations"]=viol[:50]
    res["num_violations"]=len(viol)
    res["checked_pairs"]=pairs
    res["n_scope"]=7
    json.dump(res,open("work/decisive-cayley-sweep.json","w"),indent=1)
    print("validations:",json.dumps(res["validations"])[:600])
    print("pairs checked:",pairs,"violations:",len(viol))
    if viol: print(json.dumps(viol[:5],indent=1))

if __name__=="__main__": main()
