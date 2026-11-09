# Exact minimum distance of rowCode(W20) over F_19: d<=9 iff some 11-set of coordinates has all
# eleven 10-subsets singular (a rank<10 restriction). Uses exhaustive singular 10-subset list.
import numpy as np, itertools, json
from conf_tools import rref_mod
from exhaustive_mds import batched_singular
p=19; W=np.array(json.load(open('cex20_certificate.json'))['W'],dtype=np.int64)
G,piv=rref_mod(W,p); k=len(piv); n=20
subs=np.array(list(itertools.combinations(range(n),k)))
sing=np.concatenate([batched_singular(G[:,S].transpose(1,0,2),p) for S in np.array_split(subs,8)])
bad=set(map(tuple,subs[sing].tolist())); print('singular 10-subsets',len(bad))
cnt=0
for T in itertools.combinations(range(n),11):
    if all(tuple(x for x in T if x!=y) in bad for y in T): cnt+=1
print('11-sets with rank<10 (=> weight<=9 word):',cnt)
json.dump({'singular_10_subsets':len(bad),'rank_deficient_11_sets':cnt,'k':k},open('exact_distance.json','w'))
# minimum weight among codewords vanishing on the rank-deficient 11-sets
def nullvec(M):
    # left null space of M (k x t): vectors c with c@M=0 mod p
    R,pv=rref_mod(M.T.copy(),p); free=[j for j in range(M.shape[0]) if j not in pv]
    out=[]
    for f in free:
        c=np.zeros(M.shape[0],dtype=np.int64); c[f]=1
        for i,pc in enumerate(pv): c[pc]=(-R[i,f])%p
        out.append(c)
    return out
best=None; weights={}
for T in itertools.combinations(range(n),11):
    if all(tuple(x for x in T if x!=y) in bad for y in T):
        for c in nullvec(G[:,list(T)]):
            w=(c@G)%p; wt=int((w!=0).sum()); weights[wt]=weights.get(wt,0)+1
            if best is None or wt<best[0]: best=(wt,w.tolist())
print('weights of words vanishing on rank-deficient 11-sets:',weights,'min',best)
json.dump({'singular_10_subsets':len(bad),'rank_deficient_11_sets':cnt,'k':k,'min_weight_word':best[1],'min_weight':best[0]},open('exact_distance.json','w'))
