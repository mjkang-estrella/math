# MathDB 338569 diagnostic: random n_3-configurations (lines = union of 3 random perfect matchings, linear,
# rejection sampled; labelled model, NOT uniform over isomorphism classes). Source criterion (Main Theorem):
# not magic over any abelian group iff e_p - e_q lies in the Z-row space of the line-point incidence matrix.
# For nonsingular A: iff columns p,q of (A^T)^{-1} agree modulo Z.
import sys, random, json
from fractions import Fraction
def rand_config(n,rng):
    while True:
        perms=[list(range(n)) for _ in range(3)]
        for p in perms: rng.shuffle(p)
        lines=[frozenset((perms[0][i],perms[1][i],perms[2][i])) for i in range(n)]
        if any(len(L)<3 for L in lines): continue
        ok=True; seen=set()
        for L in lines:
            for a in L:
                for b in L:
                    if a<b:
                        if (a,b) in seen: ok=False;break
                        seen.add((a,b))
        if ok: return lines
def inv_T(lines,n):
    # rows of A = lines; we need B=(A^T)^{-1}; solve via Gauss-Jordan on A^T over Q
    M=[[Fraction(int(p in L)) for L in lines]+[Fraction(int(i==p)) for i in range(n)] for p in range(n)]
    for c in range(n):
        piv=next((r for r in range(c,n) if M[r][c]!=0),None)
        if piv is None: return None
        M[c],M[piv]=M[piv],M[c]; f=M[c][c]; M[c]=[x/f for x in M[c]]
        for r in range(n):
            if r!=c and M[r][c]!=0:
                g=M[r][c]; M[r]=[a-g*b for a,b in zip(M[r],M[c])]
    return [row[n:] for row in M]
def magic(lines,n):
    B=inv_T(lines,n)
    if B is None: return None
    cols=[tuple(B[i][p]%1 for i in range(n)) for p in range(n)]
    return len(set(cols))==n
rng=random.Random(109); out={}
for n in map(int,sys.argv[2:]):
    res={'magic':0,'nonmagic':0,'singular':0}
    for t in range(int(sys.argv[1])):
        m=magic(rand_config(n,rng),n)
        res['singular' if m is None else ('magic' if m else 'nonmagic')]+=1
    out[n]=res; print(n,res,flush=True)
json.dump(out,open('outputs/magic-random-'+'-'.join(sys.argv[2:])+'.json','w'),indent=1)
