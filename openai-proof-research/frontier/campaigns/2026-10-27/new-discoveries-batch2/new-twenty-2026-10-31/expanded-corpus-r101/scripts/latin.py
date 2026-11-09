import sys,pathlib,json
import numpy as np
from scipy.optimize import linprog
from sympy import Matrix
D=pathlib.Path(__file__).resolve().parents[1];n=6;pts=[(i,j) for i in range(n) for j in range(n)];N=n*n
B=Matrix([[int(i==a) for i,j in pts] for a in range(n)]+[[int(j==a) for i,j in pts] for a in range(n)]+[[int((i+j)%n==a) for i,j in pts] for a in range(n)])
A=B.T*B-3*Matrix.eye(N);keep=[v for v in range(N) if A[0,v]==0];H=A.extract(keep,keep);BH=B.extract(range(3*n),keep)
z=BH.nullspace()[0];zfull=Matrix.zeros(N,1)
for j,v in enumerate(keep):zfull[v]=z[j]
assert H*z==-3*z
r=linprog(np.zeros(N),A_eq=np.array(B).astype(float),b_eq=np.ones(3*n),bounds=[(0,0) if A[0,j] else (0,None) for j in range(N)],method='highs',options={'threads':2})
from fractions import Fraction
x=Matrix([str(Fraction(float(t)).limit_denominator(1000)) for t in r.x]);assert B*x==Matrix.ones(3*n,1);assert all(x[i]==0 for i in range(N) if A[0,i]);assert min(x)>=0
rec={'n':n,'keep':keep,'fractional_transversal':[str(t) for t in x],'eigenvector':[str(t) for t in zfull],'checks':'B x = ones; x nonnegative; x_N(0)=0; induced eigenvector -3 exact via B z=0','graph_definition':'vertices (i,j) in Z6^2; adjacency distinct vertices sharing row,column,or cyclic symbol i+j'}
(D/'outputs/latin36-certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec)
