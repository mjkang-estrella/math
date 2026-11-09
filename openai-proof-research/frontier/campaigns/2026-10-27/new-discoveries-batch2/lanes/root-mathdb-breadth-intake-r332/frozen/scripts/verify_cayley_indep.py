# Independent re-verification, different code path: recursive enumeration + naive subsequence check.
import itertools,json
def is_cayley(w):
    return set(w)==set(range(1,max(w)+1))
def contains(w,p):
    L=len(p); n=len(w)
    for idxs in itertools.combinations(range(n),L):
        s=[w[i] for i in idxs]
        # order-isomorphic to p incl ties?
        ok=True
        for a in range(L):
            for b in range(L):
                if (s[a]<s[b])!=(p[a]<p[b]) or (s[a]==s[b])!=(p[a]==p[b]): ok=False;break
            if not ok: break
        if ok: return True
    return False
def count(n,p):
    c=0; witnesses=[]
    # enumerate all words length n over [1..n], filter cayley
    for w in itertools.product(range(1,n+1),repeat=n):
        if is_cayley(w) and not contains(w,p):
            c+=1
            if len(witnesses)<2: witnesses.append(w)
    return c
out={}
for n in [5,6]:
    a=count(n,(1,1,2,2)); b=count(n,(1,1,1,2))
    out["n=%d"%n]={"cay_1122":a,"cay_1112":b,"violates_8.8":a<b}
# also validate |Cay_4(112)| formula & Fubini totals
out["fubini5_check"]=sum(1 for w in itertools.product(range(1,5),repeat=5) if is_cayley(w))
out["cay4_112_n5"]=count(5,(1,1,2))
json.dump(out,open("work/decisive-cayley-verify.json","w"),indent=1)
print(json.dumps(out,indent=1))
