"""Independent exact verifier (no shared code with kiraly.js).
Given a 0/1 matrix A (rows = clutter edges on columns 0..n-1):
 1. checks clutter property;
 2. computes blocker b(C) by brute force over all 2^n subsets, by definition
    (transversal and no proper subset is a transversal -- checked by single-element removal,
    which suffices because transversality is upward closed);
 3. checks nonideality certificate: A square, x*=(1/r)1 feasible and tight on all rows,
    A nonsingular (exact Fraction rank);
 4. decides existence of (p,q) by full enumeration of all p in prod_X X; for each p, q exists iff
    every Y in b(C) has some v in Y not 'killed' (killed: exists X with X∩Y={v} and p(X)=v).
Also reports the variant where q(Y) may be ANY element of V (literal-typo reading).
"""
import sys, json, itertools
from fractions import Fraction

def rank(M):
    M=[[Fraction(x) for x in r] for r in M]; rk=0; rows=len(M); cols=len(M[0])
    for c in range(cols):
        piv=next((i for i in range(rk,rows) if M[i][c]!=0),None)
        if piv is None: continue
        M[rk],M[piv]=M[piv],M[rk]
        for i in range(rows):
            if i!=rk and M[i][c]!=0:
                f=M[i][c]/M[rk][c]; M[i]=[a-f*b for a,b in zip(M[i],M[rk])]
        rk+=1
    return rk

def main(A):
    n=len(A[0]); C=[frozenset(j for j in range(n) if r[j]) for r in A]
    assert all(not (X<Y) and (X!=Y or i==j) for i,X in enumerate(C) for j,Y in enumerate(C)), 'not clutter'
    def transversal(S): return all(S & X for X in C)
    B=[]
    for m in range(1<<n):
        S=frozenset(j for j in range(n) if m>>j&1)
        if transversal(S) and all(not transversal(S-{v}) for v in S): B.append(S)
    r=len(C[0]); assert all(len(X)==r for X in C)
    nonideal = len(A)==n and rank(A)==n
    def solve(qany):
        Cl=[sorted(X) for X in C]; cnt=0
        for p in itertools.product(*Cl):
            ok=True
            for Y in B:
                killed=set()
                for X,v in zip(C,p):
                    XY=X&Y
                    if len(XY)==1 and v in XY: killed.add(v)
                    if qany and v not in Y and len(XY)==1: killed.add(v)  # q(Y)=v outside Y meets X with |X∩Y|=1
                cand = (set(range(n)) if qany else set(Y)) - killed
                if not cand: ok=False; break
            if ok: return p
            cnt+=1
        return None
    p=solve(False); p2=solve(True)
    return dict(n=n,edges=len(C),blocker=len(B),blocker_sizes=sorted({len(Y) for Y in B}),
                nonsingular_square=nonideal,witness_p=p,exists_pq=p is not None,exists_pq_q_unrestricted=p2 is not None)

if __name__=='__main__':
    d=json.load(open(sys.argv[1])); n=sys.argv[2]; i=int(sys.argv[3]); A=d[n][i]
    if len(sys.argv)>4 and sys.argv[4]=='T': A=[list(c) for c in zip(*A)]
    print(json.dumps(main(A)))
