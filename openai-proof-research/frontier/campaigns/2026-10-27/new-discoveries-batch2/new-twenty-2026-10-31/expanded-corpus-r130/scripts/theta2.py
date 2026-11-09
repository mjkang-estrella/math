# MathDB 341842 (Bhatnagar-Schlosser Conjecture 1): incremental exact expansion of
#   (q,q^2;q^3)_n prod_{j=1}^m (p^j q, p^j q^2; q^3)_n (p^j q^{-1}, p^j q^{-2}; q^{-3})_n,
# truncated at p-degree K, for n=0..NMAX; checks the Borwein +-- pattern of the p^k coefficient
# (coeff of q^M must be >=0 if M=0 mod 3 and <=0 otherwise), for every k<=K and n.
import sys, json
m=int(sys.argv[1]); NMAX=int(sys.argv[2]); K=int(sys.argv[3])
P=[dict() for _ in range(K+1)]; P[0][0]=1
def mul(pd, e):
    # multiply by (1 - p^pd q^e)
    for k in range(K, -1, -1):
        if pd==0:
            src=list(P[k].items()); tgt=P[k]
        else:
            if k-pd<0: continue
            src=list(P[k-pd].items()); tgt=P[k]
        for q,v in src:
            t=q+e; nv=tgt.get(t,0)-v
            if nv: tgt[t]=nv
            else: tgt.pop(t,None)
def bad_count(k):
    b=0; first=None
    for q,v in P[k].items():
        if (v<0 and q%3==0) or (v>0 and q%3!=0):
            b+=1
            if first is None or q<first[0]: first=(q,v)
    return b,first
viol={k:[] for k in range(K+1)}
for n in range(0,NMAX+1):
    if n>0:
        i=n-1
        mul(0,3*i+1); mul(0,3*i+2)
        for j in range(1,m+1):
            if j>K: break
            for e in (3*i+1,3*i+2,-3*i-1,-3*i-2): mul(j,e)
    for k in range(K+1):
        b,f=bad_count(k)
        if b: viol[k].append([n,b,f])
    if n%5==0: print(json.dumps(dict(n=n,terms=sum(len(x) for x in P))),flush=True)
summary={k:dict(violating_n=[v[0] for v in viol[k]],last_violation=(viol[k][-1][0] if viol[k] else None),first_example=(viol[k][0] if viol[k] else None)) for k in range(K+1)}
print(json.dumps(dict(m=m,NMAX=NMAX,K=K,summary=summary)))
