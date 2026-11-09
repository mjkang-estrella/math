# 340750 / Tokushige Conjecture 1 (arXiv:1810.06820v2). Exact small checks.
# (a) literal flaw: (n,k,l)=(6,4,1) hypothesis (one orientation) holds, yet M >= 12 > C(5,3)C(5,0)=10.
# (b) brute force M(n,k,l) and all optimal pairs for (7,2,4) [intended orientation l>n/2] via superset sums over B-side? we enumerate A-side
#     masks over k-sets (C(7,2)=21 bits): f(mask)=#l-sets meeting every k-set in mask; product=popcount*f.
import itertools,json,sys
from math import comb
import numpy as np
def hyp(n,k,l):
    star=comb(n-1,k-1)*comb(n-1,l-1); out=[]
    for j in range(0,n-1):
        a=comb(n-1,k-1)+(comb(n-j-2,k-j-1) if k-j-1>=0 else 0)
        b=comb(n-1,l-1)-comb(n-j-2,l-1)
        out.append((j,a*b,star))
    return out
rep={}
h=hyp(6,4,1); rep['lit_6_4_1_hyp_all_lt_star']=all(p<s for _,p,s in h); rep['lit_6_4_1_star']=h[0][2]
rep['lit_6_4_1_competitor']=comb(4,2)*2
def brute(n,k,l):
    K=list(itertools.combinations(range(n),k)); L=list(itertools.combinations(range(n),l))
    m=len(K); cnt=np.zeros(1<<m,dtype=np.int32)
    for b in L:
        bs=set(b); mask=0
        for i,a in enumerate(K):
            if bs & set(a): mask|=1<<i
        cnt[mask]+=1
    # superset sum: g[mask] = #B with meetmask ⊇ mask
    for i in range(m):
        bit=1<<i
        v=cnt.reshape(-1,2*bit)
        v[:,:bit]+=v[:,bit:]
    pc=np.zeros(1<<m,dtype=np.int32)
    for i in range(m): pc+= (np.arange(1<<m,dtype=np.int64)>>i)&1
    prod=pc.astype(np.int64)*cnt
    M=int(prod.max()); arg=np.nonzero(prod==M)[0]
    stars=[]
    for i in range(n):
        stars.append(sum(1<<j for j,a in enumerate(K) if i in a))
    nonstar=[int(x) for x in arg if int(x) not in stars]
    return M,len(arg),nonstar[:5]
for (n,k,l) in [(7,2,4)]:
    M,na,ns=brute(n,k,l); star=comb(n-1,k-1)*comb(n-1,l-1)
    rep['%d_%d_%d'%(n,k,l)]={'M':M,'star':star,'num_optimal_A_masks':na,'nonstar_optimal_examples':ns,'hyp':hyp(n,k,l)}
print(json.dumps(rep))
