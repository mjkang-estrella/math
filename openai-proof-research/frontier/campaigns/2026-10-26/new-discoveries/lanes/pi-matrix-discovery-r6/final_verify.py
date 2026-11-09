"""Secondary check: 60-digit mpmath direct evaluation of the exact rational witness."""
import json
from fractions import Fraction as F
from mpmath import mp
mp.dps = 60
d = json.load(open('witness_exact.json'))
def ds(s): return F(s)
def deser(V): return [[complex(ds(V[i][j][0]), ds(V[i][j][1])) for j in range(3)] for i in range(len(V))]
U = deser(d['U']); X = deser(d['X'])
def M(Z): return mp.matrix([[mp.mpc(Z[i][j].real, Z[i][j].imag) for j in range(3)] for i in range(3)])
Aks = [M([[U[k][i]*X[k][j].conjugate() for j in range(3)] for i in range(3)]) for k in range(3)]
S = Aks[0]+Aks[1]+Aks[2]
D = sum(M([[X[k][i]*X[k][j].conjugate() for j in range(3)] for i in range(3)]) for k in range(3))
# singular values of S = sqrt(eig(S^H S)); both S^H S and D are complex Hermitian -> use mp.eig
SHS = S.H*S
ev1 = mp.eig(SHS)[0]
sv = sorted([mp.sqrt(z.real) for z in ev1], reverse=True)
ev = mp.eig(D)
evD = sorted([z.real for z in ev[0]])
num = (sum(s**(mp.mpf(5)/4) for s in sv))**(mp.mpf(4)/5)
den = (sum(e**(mp.mpf(5)/4) for e in evD))**(mp.mpf(4)/5)
print("||S||_{5/4}   =", mp.nstr(num, 30))
print("||D||_{5/4}   =", mp.nstr(den, 30))
print("ratio         =", mp.nstr(num/den, 30))
f = lambda t: t**(mp.mpf(5)/4) - 2*t - 2
x = mp.findroot(f, 19.5)
c = mp.sqrt(x*(x+2))/((x**(mp.mpf(5)/4)+2)**(mp.mpf(4)/5))
print("c_{5/4}(3)    =", mp.nstr(c, 30))
print("excess        =", mp.nstr(num/den - c, 20))
