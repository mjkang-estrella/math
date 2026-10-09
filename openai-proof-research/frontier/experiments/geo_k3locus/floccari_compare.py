"""Compare the corpus locus (T -> V_P = U^2+<-1>^4) with Floccari's published locus
(T -> W_m = U^3+<-m>, some m>0; Geometry & Topology 30 (2026), Thm 5.11).
Checks embeddings by local invariants (Hasse-Minkowski), searching complements.
Run: python3 -I floccari_compare.py
"""
exec(open('vp_embedding.py').read().split('# cross-check')[0])
import random, math
def embeds(T, V, X=400):
    """Does T embed isometrically in V?  Searches diagonal complements with entries |.|<=X
    when complement rank<=2; for complement rank>=3 local invariants are always realizable."""
    k=len(V)-len(T)
    pos_T=sum(1 for a in T if a>0); pos_V=sum(1 for a in V if a>0)
    neg_T=len(T)-pos_T; neg_V=len(V)-pos_V
    sp,sn=pos_V-pos_T,neg_V-neg_T
    if sp<0 or sn<0: return False
    dT=math.prod(T); dV=math.prod(V)
    if k==0:
        return sqfree(dT)==sqfree(dV) and all(hasse(T,p)==hasse(V,p) for p in set(relevant_primes(T+V))|{2})
    if k>=3: return True
    signs=[1]*sp+[-1]*sn
    if k==1:
        x=signs[0]*abs(sqfree(dV*dT))
        if (x>0)!=(signs[0]>0): return False
        N=[x]
        if sqfree(dT*x)!=sqfree(dV): return False
        return all(hasse(T+N,p)==hasse(V,p) for p in set(relevant_primes(T+N+V))|{2})
    # k==2
    for a in range(1,X+1):
        x=signs[0]*a
        y=signs[1]*abs(sqfree(dV*dT*x))
        N=[x,y]
        if sqfree(dT*x*y)!=sqfree(dV): continue
        if all(hasse(T+N,p)==hasse(V,p) for p in set(relevant_primes(T+N+V))|{2}):
            return True
    return False
VP=[1,-1,1,-1,-1,-1,-1,-1]
def W(m): return [1,-1,1,-1,1,-1,-m]

def floccari_search(T, positive_expected):
    lim = 200000 if positive_expected else 3000
    for m in range(1, lim):
        if embeds(T, W(m)): return m
    return None
random.seed(7)
pool=[1,2,3,5,6,7,10,11,13,14,15,17,19,21,22,23]
for _ in range(60):
    T=[random.choice(pool) for _ in range(2)]+[-random.choice(pool) for _ in range(3)]
    assert embeds(T,VP)
    assert floccari_search(T, True) is not None, T
print("rank-5: 60/60 samples embed in V_P and in some W_m")
def odd_split_bad(T):
    d=math.prod(T)
    return [p for p in relevant_primes(T) if p!=2 and is_local_square(-d,p) and hasse(T,p)==-1]
def two_splits(T):
    return is_local_square(-math.prod(T),2)
random.seed(11)
cnt={'both':0,'corpus_only':0,'floccari_only':0,'neither':0}
for _ in range(300):
    T=[random.choice(pool) for _ in range(2)]+[-random.choice(pool) for _ in range(4)]
    union_pred = (len(odd_split_bad(T))==0)
    floc_pred = union_pred and (not two_splits(T) or hasse(T,2)==-1)
    corp_pred = (not criterion6(T))
    a = embeds(T,VP,X=3000) if corp_pred else embeds(T,VP,X=500)
    m = floccari_search(T, floc_pred)
    b = m is not None
    assert a==corp_pred, ("corpus",T)
    assert b==floc_pred, ("floccari",T,m)
    assert (a or b)==union_pred
    if a!=b: assert two_splits(T)
    key=('both' if a and b else 'corpus_only' if a else 'floccari_only' if b else 'neither')
    cnt[key]+=1
print("rank-6 theory check passed on 300 samples:",cnt)
for T in ([21,2,-6,-19,-2,-10],[3,2,-13,-10,-3,-15],[19,13,-21,-14,-14,-21],[14,1,-21,-5,-7,-14],[15,22,-1,-11,-7,-7]):
    print(T,"K=Q(sqrt(%d))"%sqfree(-math.prod(T)),"2 splits:",two_splits(T),"c_2:",hasse(T,2),
          "odd split primes with e2!=0:",odd_split_bad(T),"in V_P:",not criterion6(T))
