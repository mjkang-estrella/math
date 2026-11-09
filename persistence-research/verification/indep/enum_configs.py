# Independent enumeration of Level-1 configurations and the cheap mod-8 / mod-5 parity kill.
# Config = placement of non-1 digits (digit in {2,3,4}) with product in {4,6,8,9}, >=2 non-1 digits.
import itertools
mults=[(2,2),(2,3),(2,4),(3,3),(2,2,2)]
for m in mults:
    pr=1
    for d in m: pr*=d
    assert pr in (4,6,8,9)
# all multisets of size>=2 from {2,3,4} with product in {4,6,8,9}
allm=[]
for k in range(2,8):
    for c in itertools.combinations_with_replacement((2,3,4),k):
        pr=1
        for d in c: pr*=d
        if pr in (4,6,8,9): allm.append(c)
print("multisets:",allm); assert sorted(allm)==sorted(mults)
def parity_ok(K):
    # exists (t,a,w) with 2^t 3^a 7^w = K mod 8 and mod 5 (t>=0 arbitrary, K!=0 mod 5)
    if K%5==0: return False
    for t in range(0,12):
        for a in range(0,8):
            for w in range(0,8):
                v=2**t*3**a*7**w
                if (v-K)%8==0 and (v-K)%5==0: return True
    return False
# one-far and two-far configurations: far positions >=3, low positions in {0,1,2}
res={}
for m in mults:
    k=len(m)
    for nlow in range(0,k+1):
        # choose which digits are low (as a multiset-of-positions assignment): enumerate ordered placements
        for lowidx in itertools.combinations(range(k),nlow):
            for lowpos in itertools.permutations(range(3),nlow):
                S=sum((m[i]-1)*10**p for i,p in zip(lowidx,lowpos))
                far=[m[i]-1 for i in range(k) if i not in lowidx]
                key=(tuple(sorted(far)),S)
                res.setdefault(key,set()).add(m)
rows=sorted(res)
print("(far c-values, S_low) -> multisets, parity_ok(K=9S-1)  [far=() means all-low, S>0]")
for key in rows:
    far,S=key
    K=9*S-1
    print(far,S,K,sorted(res[key]),parity_ok(K) if far else "all-low")
