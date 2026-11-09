"""Exact independent check (jeu de taquin DP, verify_minors.mm) that two hook words give equal multisets of k-minors."""
import sys; sys.path.insert(0,'scripts')
from verify_minors import mm, is_syt
def hook(bits):  # bits: string, position j (1-based) -> entry j+1; '1' = leg
    arm=[1]+[j+2 for j,b in enumerate(bits) if b=='0']; legs=[(j+2,) for j,b in enumerate(bits) if b=='1']
    return tuple([tuple(arm)]+legs)
k=int(sys.argv[1])
for a,b in zip(sys.argv[2::2],sys.argv[3::2]):
    T,U=hook(a),hook(b); n=len(a)+1; A,B=mm(T,k),mm(U,k)
    print('n',n,'k',k,'T',T,'U',U,'SYT',is_syt(T,n),is_syt(U,n),'distinct',T!=U,'equal mM_k:',A==B,'total',sum(c for _,c in A))
