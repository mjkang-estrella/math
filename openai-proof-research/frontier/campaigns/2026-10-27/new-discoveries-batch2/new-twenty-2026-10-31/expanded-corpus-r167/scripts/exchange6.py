# sanity: bases of R_6 minus a symmetric family satisfy basis exchange? (prism family: expected yes; control: K33 family also free)
import itertools,json
n=6; P=list(itertools.combinations(range(n),2)); idx={e:i for i,e in enumerate(P)}
def laman(mask):
    E=[P[i] for i in range(len(P)) if (mask>>i)&1]
    for k in range(2,n+1):
        for X in itertools.combinations(range(n),k):
            s=set(X)
            if sum(1 for a,b in E if a in s and b in s)>2*k-3: return False
    return True
bases=[m for c in itertools.combinations(range(len(P)),2*n-3) for m in [sum(1<<i for i in c)] if laman(m)]
def orbit(E):
    out=set()
    for p in itertools.permutations(range(n)):
        out.add(sum(1<<idx[tuple(sorted((p[a],p[b])))] for a,b in E))
    return out
prism=[(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)]
k33=[(a,b) for a in range(3) for b in range(3,6)]
def exch(B):
    S=set(B)
    for B1 in B:
        for B2 in B:
            d1=B1&~B2
            m=d1
            while m:
                x=m&-m; m&=m-1
                d2=B2&~B1; ok=False; m2=d2
                while m2:
                    y=m2&-m2; m2&=m2-1
                    if (B1&~x)|y in S: ok=True; break
                if not ok: return False
    return True
res={'R6_bases':len(bases)}
for name,E in [('prism',prism),('K33',k33)]:
    O=orbit(E); Bp=[b for b in bases if b not in O]
    res[name]={'orbit':len(O),'remaining':len(Bp),'exchange_ok':exch(Bp)}
# control: removing a non-free basis (K4-e plus ...): take a Laman basis containing a tight 4-set
ctl=[(0,1),(0,2),(0,3),(1,2),(1,3),(0,4),(1,4),(0,5),(1,5)]
O=orbit(ctl); Bp=[b for b in bases if b not in O]
res['control_nonfree']={'is_basis':sum(1<<idx[e] for e in ctl) in set(bases),'orbit':len(O),'exchange_ok':exch(Bp)}
print(json.dumps(res))
