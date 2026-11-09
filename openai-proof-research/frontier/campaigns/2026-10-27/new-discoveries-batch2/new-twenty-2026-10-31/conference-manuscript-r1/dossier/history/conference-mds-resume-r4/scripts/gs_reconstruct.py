# Rebuild W20 from the Goethals-Seidel array with the four +-1 sequences; compare to frozen matrix.
# Usage: python3 -I gs_reconstruct.py <cex_20.json> <cex20_certificate.json>
import json, sys
a,b,c,d=json.load(open(sys.argv[1]))['seqs']; W0=json.load(open(sys.argv[2]))['W']; m=5
circ=lambda r:[[r[(j-i)%m] for j in range(m)] for i in range(m)]
mul=lambda X,Y:[[sum(X[i][t]*Y[t][j] for t in range(m)) for j in range(m)] for i in range(m)]
T=lambda X:[list(r) for r in zip(*X)]; N=lambda X:[[-x for x in r] for r in X]
R=[[int(i+j==m-1) for j in range(m)] for i in range(m)]
A,B,C,D=map(circ,(a,b,c,d))
BL=[[A,mul(B,R),mul(C,R),mul(D,R)],[N(mul(B,R)),A,mul(T(D),R),N(mul(T(C),R))],
    [N(mul(C,R)),N(mul(T(D),R)),A,mul(T(B),R)],[N(mul(D,R)),mul(T(C),R),N(mul(T(B),R)),A]]
H=[sum((BL[I][J][i] for J in range(4)),[]) for I in range(4) for i in range(m)]
W=[[H[i][j]-int(i==j) for j in range(20)] for i in range(20)]
print('sequences',a,b,c,d); print('GS reconstruction equals frozen matrix:',W==W0)
paf=lambda s,t:sum(s[i]*s[(i+t)%m] for i in range(m))
print('PAF sums t=1..4:',[paf(a,t)+paf(b,t)+paf(c,t)+paf(d,t) for t in range(1,m)], 'a skew-type:',all(a[(m-i)%m]==-a[i] for i in range(1,m)))
