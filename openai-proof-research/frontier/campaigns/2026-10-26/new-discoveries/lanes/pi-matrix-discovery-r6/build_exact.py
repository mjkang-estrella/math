"""Build the exact rational witness (columns exactly unit norm in Q[i]) and save as JSON."""
import numpy as np, json
from fractions import Fraction as F
from scipy.optimize import brentq

Ur = np.load('witness_u_rational.npy'); Xr = np.load('witness_x_rational.npy')

def rat_unit_near(w, nd):
    w = np.asarray(w, dtype=float).ravel()
    if abs(1+w[5]) < 1e-9: w = w[::-1].copy()
    r = w[:5]/(1+w[5])
    r = [F(round(v*10**nd), 10**nd) for v in r]
    s2 = sum(v*v for v in r); den = 1+s2
    return [2*v/den for v in r] + [(1-s2)/den]

def to_rat(z, nd):
    z = z/np.linalg.norm(z)
    w = np.concatenate([z.real, z.imag])
    out = rat_unit_near(w, nd)
    return [(out[i], out[i+3]) for i in range(3)]  # list of (re,im) Fractions

def norm2(Vc):  # Vc: list of 3 columns, each list of 3 (re,im)
    return [sum(Vc[k][j][0]**2 + Vc[k][j][1]**2 for j in range(3)) for k in range(3)]

def cmul(a, b):  # (re,im) product
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def cconj(a): return (a[0], -a[1])
def cadd(a, b): return (a[0]+b[0], a[1]+b[1])
ZERO = (F(0), F(0))

best=None
for nd in range(3,11):
    Us=[to_rat(Ur[:,k],nd) for k in range(3)]   # Us[k] = column k, list of 3 (re,im)
    Xs=[to_rat(Xr[:,k],nd) for k in range(3)]
    nu, nx = norm2(Us), norm2(Xs)
    assert all(v==1 for v in nu) and all(v==1 for v in nx), (nu, nx)
    # A_k = u_k x_k^* : (A_k)_{ij} = u_k[i] * conj(x_k[j])
    Aks=[[[cmul(Us[k][i], cconj(Xs[k][j])) for j in range(3)] for i in range(3)] for k in range(3)]
    S=[[cadd(cadd(Aks[0][i][j],Aks[1][i][j]),Aks[2][i][j]) for j in range(3)] for i in range(3)]
    # M1 = S^* S: (S^*S)_{ij} = sum_r conj(S[r][i]) S[r][j]
    M1=[[cadd(cadd(cmul(cconj(S[0][i]),S[0][j]),cmul(cconj(S[1][i]),S[1][j])),cmul(cconj(S[2][i]),S[2][j])) for j in range(3)] for i in range(3)]
    # D = sum_k x_k x_k^*: (D)_{ij} = sum_k x_k[i] conj(x_k[j])
    D=[[cadd(cadd(cmul(Xs[0][i],cconj(Xs[0][j])),cmul(Xs[1][i],cconj(Xs[1][j]))),cmul(Xs[2][i],cconj(Xs[2][j]))) for j in range(3)] for i in range(3)]
    # numeric ratio
    M1n=np.array([[float(M1[i][j][0])+1j*float(M1[i][j][1]) for j in range(3)] for i in range(3)])
    Dn=np.array([[float(D[i][j][0])+1j*float(D[i][j][1]) for j in range(3)] for i in range(3)])
    assert np.abs(M1n-M1n.conj().T).max() < 1e-12 and np.abs(Dn-Dn.conj().T).max() < 1e-12
    l1=np.linalg.eigvalsh(M1n); l2=np.linalg.eigvalsh(Dn)
    R=((l1**0.625).sum())**(1/1.25)/((l2**1.25).sum())**(1/1.25)
    x=brentq(lambda t: t**1.25-2*t-2,1.0000001,1e7); cf=np.sqrt(x*(x+2))/((x**1.25+2)**(1/1.25))
    e=R-cf
    print(f"nd={nd}: excess {e:.5e}")
    if best is None or e>best[0]: best=(e,Us,Xs,nd)
e,Us,Xs,nd = best
print("best nd:", nd, "excess:", e)
def ser(V): return [[[str(re), str(im)] for (re,im) in col] for col in V]
json.dump({'U':ser(Us),'X':ser(Xs),'nd':nd}, open('witness_exact.json','w'))
print("saved")
