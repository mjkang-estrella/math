# Count projective codewords of weight 9 and 10 in rowCode(W20) over F_19. Usage: python3 -I low_weight_count.py <verify_from_scratch.json>
import json, sys, itertools
p=19; n=20; k=10
B=json.load(open(sys.argv[1]))['rref_basis']
def rref(M):
    M=[[x%p for x in r] for r in M]; r=0; piv=[]
    for c in range(len(M[0])):
        pr=next((i for i in range(r,len(M)) if M[i][c]),None)
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]; iv=pow(M[r][c],p-2,p); M[r]=[x*iv%p for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]: f=M[i][c]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
    return M[:r],piv
words={}
for S in itertools.combinations(range(n),k):
    R,pv=rref([[B[i][s] for i in range(k)] for s in S]); free=[j for j in range(k) if j not in pv]
    if not free: continue
    assert len(free)==1
    c=[0]*k; c[free[0]]=1
    for i,pc in enumerate(pv): c[pc]=(-R[i][free[0]])%p
    w=[sum(c[i]*B[i][j] for i in range(k))%p for j in range(n)]
    f=next(x for x in w if x); iv=pow(f,p-2,p); w=tuple(x*iv%p for x in w)
    words[w]=sum(1 for x in w if x)
from collections import Counter
cnt=Counter(words.values()); print('projective low-weight words by weight:',dict(cnt),'(times 18 for all nonzero scalar multiples)')
supp9=[tuple(j for j in range(n) if w[j]) for w,wt in words.items() if wt==9]
print('example weight-9 supports:',supp9[:5])
