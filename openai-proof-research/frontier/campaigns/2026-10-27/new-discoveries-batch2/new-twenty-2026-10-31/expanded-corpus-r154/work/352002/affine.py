# Cross-check: a_m = #{FC affine permutations w in A~_{n-1} that are the unique minimal-length element of w*K_m},
# K_m = {translations t_{m beta}}. Uses Shi's length formula and checks beta = +-chi_S (L-natural convexity).
import sys,itertools
from collections import Counter
m=int(sys.argv[1]); n=int(sys.argv[2]); Lmax=int(sys.argv[3])
def length(win):
    return sum(abs((win[j]-win[i])//n) for i in range(n) for j in range(i+1,n))
def rmul_gen(win,s):
    w=list(win)
    if s<n-1: w[s],w[s+1]=w[s+1],w[s]
    else:  # s_0: swaps positions 0 and 1 (i.e. values at n and n+1): w(1)<->w(0)=w(n)-n
        w[0],w[n-1]=w[n-1]-n,w[0]+n
    return tuple(w)
gens=list(range(n))  # 0..n-2 = s_1..s_{n-1}; n-1 = s_0
def commute(a,b):
    # in A~_{n-1} (n>=3): generators i,j commute iff not adjacent on the n-cycle
    ia = a+1 if a<n-1 else 0; ib = b+1 if b<n-1 else 0
    return a!=b and (ia-ib)%n not in (1,n-1)
comm=[[commute(a,b) for b in gens] for a in gens]
def append(F,s):
    j=-1
    for idx in range(len(F)-1,-1,-1):
        if any(not comm[s][t] for t in F[idx]): j=idx; break
    F=list(F)
    if j+1==len(F): F.append(frozenset([s]))
    else: F[j+1]=F[j+1]|{s}
    return tuple(F)
I=tuple(range(1,n+1))
foata={I:()}; layer=[I]; lens={I:0}; L=0; fc=[I]
while L<Lmax:
    nxt={}
    for g in layer:
        for s in gens:
            h=rmul_gen(g,s)
            if h in lens: continue
            nxt.setdefault(h,[]).append((g,s))
    L+=1; layer=[]
    for h,preds in nxt.items():
        lens[h]=L; layer.append(h)
        forms=set(); ok=True
        for g,s in preds:
            if foata.get(g) is None: ok=False; break
            forms.add(append(foata[g],s))
            if len(forms)>1: ok=False; break
        foata[h]=next(iter(forms)) if ok else None
        if ok: fc.append(h)
B=int(sys.argv[4]) if len(sys.argv)>4 else 2
betas=[b for b in itertools.product(range(-B,B+1),repeat=n) if sum(b)==0 and any(b)]
cnt=Counter()
for w in fc:
    lw=lens[w]; uniq=True
    for b in betas:
        w2=[w[i]+m*n*b[i] for i in range(n)]
        if length(w2)<=lw: uniq=False; break
    if uniq: cnt[lw]+=1
tot=sum(cnt.values())
print({'m':m,'n':n,'Lmax':Lmax,'fc_affine_upto_Lmax':len(fc),'a_m_via_lifts':tot,'by_length':[cnt[l] for l in range(Lmax+1)]})
