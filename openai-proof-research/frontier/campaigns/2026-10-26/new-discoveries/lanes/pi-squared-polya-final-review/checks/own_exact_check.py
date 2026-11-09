"""REVIEWER-OWN independent exact/numeric re-derivation. Not a rerun of parent's script.

Checks, from scratch:
 1. input bounds for U=diag(A,B), V=diag(B,I) on [1,1024]
 2. Riccati identity (A+B)A^-1(A+B) = (1054721/2048) B  (exact Fractions)
 3. A#B = (A+B)/s   via INDEPENDENT eigendecomposition (mpmath, 60 digits)
 4. B#I = diag(32,1) via eigendecomposition
 5. F#G = (G+dF)/sqrt(r+2d) via eigendecomposition
 6. Phi images and defect matrix D = alpha^2 C^2 - D^2, quadratic form at v=(1,2)
    in pure Fraction interval arithmetic (own implementation)
 7. high-precision true value of the defect scalar
 8. exact coarse rational bound -1763270875137191128175507/102858162597360173056
 9. Diaz t=16 supplementary witness
10. Hoa-Binh-Ho 2015 Remark 1 example is POSITIVE definite at stated bounds
11. arXiv 1610.04162 p5 example violates its stated m=1 bound
"""
from fractions import Fraction as F
import mpmath as mp
mp.mp.dps = 60

R = F
def mat(x):  # list of lists of Fractions
    return [[R(v) for v in row] for row in x]

def mmul(X, Y):
    n, m, p = len(X), len(Y), len(Y[0])
    return [[sum(X[i][k]*Y[k][j] for k in range(m)) for j in range(p)] for i in range(n)]
def madd(X, Y): return [[X[i][j]+Y[i][j] for j in range(len(X[0]))] for i in range(len(X))]
def smul(c, X): return [[c*v for v in row] for row in X]
def msub(X, Y): return [[X[i][j]-Y[i][j] for j in range(len(X[0]))] for i in range(len(X))]
def eye(n): return [[R(1) if i == j else R(0) for j in range(n)] for i in range(n)]
def tr(X): return sum(X[i][i] for i in range(len(X)))
def det2(X): return X[0][0]*X[1][1] - X[0][1]*X[1][0]
def inv2(X):
    d = det2(X)
    return [[X[1][1]/d, -X[0][1]/d], [-X[1][0]/d, X[0][0]/d]]

results = {}
def check(name, cond):
    results[name] = bool(cond)
    print(("PASS " if cond else "FAIL ") + name)

# ---------- construction ----------
t = 32; h = t*t
A = mat([[R(1025, 2), R(-1023, 2)], [R(-1023, 2), R(1025, 2)]])   # I+1023*P
B = mat([[R(1024), 0], [0, R(1)]])                                # I+1023*Q
P = mat([[R(1, 2), R(-1, 2)], [R(-1, 2), R(1, 2)]])
Q = mat([[R(1), 0], [0, R(0)]])
check("P*P=P", mmul(P, P) == P)
check("Q*Q=Q", mmul(Q, Q) == Q)
check("A=I+1023P", madd(eye(2), smul(R(1023), P)) == A)
check("B=I+1023Q", madd(eye(2), smul(R(1023), Q)) == B)
check("A eigenvalues {1,1024}: A^2-1025A+1024I=0",
      madd(madd(mmul(A, A), smul(R(-1025), A)), smul(R(1024), eye(2))) ==
      [[R(0)]*2 for _ in range(2)])
check("B eigenvalues {1,1024}: B^2-1025B+1024I=0",
      madd(madd(mmul(B, B), smul(R(-1025), B)), smul(R(1024), eye(2))) ==
      [[R(0)]*2 for _ in range(2)])
check("A,B symmetric (real entries)", all(A[i][j] == A[j][i] for i in range(2) for j in range(2)) and
      all(B[i][j] == B[j][i] for i in range(2) for j in range(2)))

Fm = smul(R(1, 2), madd(A, B))          # Phi(U)
G = smul(R(1, 2), madd(B, eye(2)))      # Phi(V)
T = mat([[R(32), 0], [0, R(1)]])        # B#I
check("T^2=B", mmul(T, T) == B)

# ---------- 2. Riccati identity ----------
ss = R(1054721, 2048)
check("(A+B)A^-1(A+B) = (1054721/2048) B", mmul(mmul(madd(A, B), inv2(A)), madd(A, B)) == smul(ss, B))
check("det A = det B = 1024", det2(A) == 1024 and det2(B) == 1024)

# ---------- 3/4/5. independent eigendecomposition check of the three means ----------
def mp_mat(X): return mp.matrix([[mp.mpf(str(v.numerator))/mp.mpf(str(v.denominator)) for v in row] for row in X])
def geomean_ev(X, Y):
    """A#B by spectral square roots, 60 digits."""
    Xf, Yf = mp_mat(X), mp_mat(Y)
    # symmetric sqrt of X via eigh
    w, Vv = mp.eigsy(Xf)
    S = Vv * mp.diag([mp.sqrt(x) for x in w]) * Vv.T
    Si = Vv * mp.diag([1/mp.sqrt(x) for x in w]) * Vv.T
    J = Si * Yf * Si
    w2, V2 = mp.eigsy(J)
    Rt = V2 * mp.diag([mp.sqrt(x) for x in w2]) * V2.T
    return S * Rt * S

AB_ev = geomean_ev(A, B)
s = mp.sqrt(mp.mpf(ss.numerator)/mp.mpf(ss.denominator))
AB_ric = (mp_mat(A) + mp_mat(B)) / s
check("A#B = (A+B)/s  (eigendecomposition vs Riccati, <1e-40)",
      max(abs(AB_ev[i, j] - AB_ric[i, j]) for i in range(2) for j in range(2)) < mp.mpf('1e-40'))

BI_ev = geomean_ev(B, eye(2))
check("B#I = diag(32,1) (eigendecomposition, <1e-40)",
      max(abs(BI_ev[i, j] - (mp.mpf(32) if i == j == 0 else mp.mpf(1) if i == j else mp.mpf(0)))
          for i in range(2) for j in range(2)) < mp.mpf('1e-40'))

dd = R(4100, 1054721)
r = tr(mmul(inv2(Fm), G))
check("d^2 = det G / det F", dd == det2(G)/det2(Fm))
check("r = 1058821/1054721", r == R(1058821, 1054721))
FG_ev = geomean_ev(Fm, G)
rho = mp.mpf(r.numerator)/mp.mpf(r.denominator) + 2*mp.sqrt(mp.mpf(dd.numerator)/mp.mpf(dd.denominator))
FG_ric = (mp_mat(G) + mp.sqrt(mp.mpf(dd.numerator)/mp.mpf(dd.denominator))*mp_mat(Fm)) / mp.sqrt(rho)
check("F#G = (G+dF)/sqrt(r+2d)  (eigendecomposition vs Riccati, <1e-40)",
      max(abs(FG_ev[i, j] - FG_ric[i, j]) for i in range(2) for j in range(2)) < mp.mpf('1e-40'))

# ---------- 6. exact interval quadratic form (own implementation) ----------
def qf_exact(Mv, v=(1, 2)):
    return (Mv[0][0]*v[0]*v[0] + Mv[0][1]*v[0]*v[1] + Mv[1][0]*v[1]*v[0] + Mv[1][1]*v[1]*v[1])

# interval arithmetic on the scalar defect
def isqrt_frac(q):
    from math import isqrt
    den = 10**14
    k = isqrt(q.numerator*den*den // q.denominator)
    return F(k, den), F(k+1, den)

a2 = R(2048, 1054721); d2v = dd
aI = isqrt_frac(a2); bI = isqrt_frac(d2v)
alpha2 = R(1025, 64)**2
qF2 = qf_exact(mmul(Fm, Fm)); qFT = qf_exact(mmul(Fm, T)); qTF = qf_exact(mmul(T, Fm))
qT2 = qf_exact(mmul(T, T)); qG2 = qf_exact(mmul(G, G)); qGF = qf_exact(mmul(G, Fm)); qFG = qf_exact(mmul(Fm, G))
# interval helpers
def iadd(x, y): return (x[0]+y[0], x[1]+y[1])
def imul(x, y):
    vals = [x[0]*y[0], x[0]*y[1], x[1]*y[0], x[1]*y[1]]
    return (min(vals), max(vals))
def isub(x, y): return (x[0]-y[1], x[1]-y[0])
def iinv(x):
    assert x[0] > 0
    return (1/x[1], 1/x[0])

cp = iadd(iadd((qF2*a2, qF2*a2), imul(aI, ((qFT+qTF)/2, (qFT+qTF)/2))), (qT2/4, qT2/4))
num = iadd(iadd((qG2, qG2), imul(bI, ((qGF+qFG), (qGF+qFG)))), (d2v*qF2, d2v*qF2))
dp = imul(num, iinv(iadd((r, r), imul((2, 2), bI))))
defect = isub(imul((alpha2, alpha2), cp), dp)
check("interval defect upper bound < -17000", defect[1] < -17000)
print("   interval defect:", defect[0], "..", defect[1])
print("   decimal:", float(defect[0]), "..", float(defect[1]))

# ---------- 7. true value, 60 digits ----------
av = mp.sqrt(mp.mpf(a2.numerator)/mp.mpf(a2.denominator))
bv = mp.sqrt(mp.mpf(d2v.numerator)/mp.mpf(d2v.denominator))
rv = mp.mpf(r.numerator)/mp.mpf(r.denominator)
cpv = alpha2.numerator/mp.mpf(alpha2.denominator) * (mp.mpf(a2.numerator)/mp.mpf(a2.denominator)*mp.mpf(qF2.numerator)/mp.mpf(qF2.denominator) + av*mp.mpf((qFT+qTF).numerator)/mp.mpf((qFT+qTF).denominator)/2 + mp.mpf(qT2.numerator)/mp.mpf(qT2.denominator)/4)
dpv = (mp.mpf(qG2.numerator)/mp.mpf(qG2.denominator) + bv*mp.mpf((qGF+qFG).numerator)/mp.mpf((qGF+qFG).denominator) + mp.mpf(d2v.numerator)/mp.mpf(d2v.denominator)*mp.mpf(qF2.numerator)/mp.mpf(qF2.denominator)) / (rv + 2*bv)
print("   true defect (60 dps):", cpv - dpv)
check("true defect < -17000 strictly (margin > 50)", cpv - dpv < -17000)

# ---------- 8. coarse rational bound reproduction ----------
C = R(2048, 1054721)*R(1058845, 8) + R(441, 10000)*R(17463, 2) + R(257)
L = R(1050641, 4) + R(623, 10000)*R(1056799, 4) + R(4100, 1054721)*R(1058845, 8)
U = R(1058821, 1054721) + 2*R(624, 10000)
coarse = alpha2*C - L/U
target = -F(1763270875137191128175507, 102858162597360173056)
check("coarse bound == -1763270875137191128175507/102858162597360173056", coarse == target)
check("coarse bound < -17000", coarse < -17000)
print("   coarse:", coarse, "=", float(coarse))

# ---------- 9. Diaz t=16 witness ----------
A2 = mat([[R(257, 2), R(255, 2)], [R(255, 2), R(257, 2)]])
B2 = mat([[R(256), 0], [0, R(1)]])
C2 = smul(R(1, 2), madd(A2, mat([[R(16), 0], [0, R(1)]])))
M2 = (madd(madd(eye(2), smul(2, A2)), B2))
M2 = [[M2[i][j]/4 for j in range(2)] for i in range(2)]
E = msub(smul(R(257, 32)**2, mmul(C2, C2)), mmul(M2, M2))
val = qf_exact(E, (19, -20))
check("Diaz witness v^T E v = -2449502775/8192", val == -F(2449502775, 8192))

# ---------- 10. Hoa 2015 example positive definite at stated bounds ----------
Xh = mat([[R(5, 6), R(2)], [R(2), R(5)]])
Yh = mat([[R(1), R(3)], [R(3), R(10)]])
mH, MH = R(1, 50), R(11)
check("Hoa X in [1/50, 11]", (Xh[0][0]-mH) > 0 and det2(msub(smul(MH, eye(2)), Xh)) > 0 and (Xh[1][1]-mH) > 0)
check("Hoa Y in [1/50, 11]", (Yh[0][0]-mH) > 0 and det2(msub(smul(MH, eye(2)), Yh)) > 0 and (Yh[1][1]-mH) > 0)
dh = mp.sqrt(mp.mpf((Yh[0][0]*Yh[1][1]-Yh[0][1]*Yh[1][0]).numerator) / mp.mpf((Yh[0][0]*Yh[1][1]-Yh[0][1]*Yh[1][0]).denominator) / (mp.mpf(det2(Xh).numerator)/mp.mpf(det2(Xh).denominator)))
check("d^2 = det Y/det X = 6", det2(Yh)/det2(Xh) == 6)
K = R(303601, 2200)
check("K(h) = (11+1/50)^2/(4*11/50) = 303601/2200", K == (MH+mH)**2/(4*MH*mH))
# X#Y = (Y + d X)/sqrt(r+2d), r = tr(X^-1 Y)
rh = tr(mmul(inv2(Xh), Yh))
diff = msub(smul(K, smul(R(1, 1), mmul(madd(Yh, smul(R(0), Xh), ), Xh))), mmul(madd(Xh, Yh), eye(2)))  # placeholder, real check below
# exact leading minor and determinant of K(X#Y)^2 - (X grad Y)^2 with X#Y=(Y+dX)/sqrt(r+2d), grad=(X+Y)/2
# K*(Y+dX)^2/(r+2d) - ((X+Y)/2)^2 ; d=sqrt6, r+2d = r+2sqrt6
# (K*(Y^2 + 2d Y X + 6 X)/(r+2*sqrt6)) - (X+Y)^2/4
# Use sympy for exact radical arithmetic
import sympy as S
Xs = S.Matrix([[S.Rational(5, 6), 2], [2, 5]]); Ys = S.Matrix([[1, 3], [3, 10]])
dS = S.sqrt(6); rS = S.trace(Xs.inv()*Ys)
Ks = S.Rational(303601, 2200)
Ds = S.simplify(Ks*(Ys + dS*Xs)**2/(rS + 2*dS) - ((Xs+Ys)/2)**2)
pS = S.simplify(Ds[0, 0]); detS = S.simplify(Ds.det())
check("Hoa diff leading minor > 0", pS.is_positive)
check("Hoa diff determinant > 0", detS.is_positive)
print("   Hoa minor:", pS, " det:", detS)
check("Hoa minor matches parent", pS == S.Rational(910803)*S.sqrt(6)/S.Integer(8000) + S.Rational(95141243, 198000))
check("Hoa det matches parent", detS == S.Rational(88033691903, 87120000) + S.Rational(10018833)*S.sqrt(6)/S.Integer(12800))

# ---------- 11. arXiv 1610.04162 p5 example violates stated m=1 ----------
Xe = S.Matrix([[S.Rational(688, 10000), S.Rational(-1082, 10000)], [S.Rational(-1082, 10000), S.Rational(1998, 10000)]])
ev = Xe.eigenvals()
min_ev = min([k.evalf() for k in ev])
check("1610.04162 X min eigenvalue < 1 = stated m", min_ev < 1)
print("   min eig:", min_ev)

print()
fails = [k for k, v in results.items() if not v]
print("TOTAL:", len(results), "FAILS:", len(fails), fails if fails else "")
