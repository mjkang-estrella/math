#!/usr/bin/env python3
"""Independent adversarial exact checker for the prospective Lin Conjecture 4.3
counterexample (MathDB 332939, arXiv:1604.04141).

Rewritten from scratch (fractions.Fraction only, no reuse of parent code).
Conjecture 4.3 (verified visually from PDF p.6): for A,B n x n positive
semidefinite,  lambda(A^2+|BA|^p) >-majorizes lambda(A^2+|AB|^p)  for all p>0,
where |X|=(X*X)^(1/2) and eigenvalues are sorted descending.

A counterexample at p=3 needs:  NOT (lambda(L) succ lambda(R)),
L = A^2+|BA|^3, R = A^2+|AB|^3.
Strategy: tr L = tr R and lambda_min(L) > tau > lambda_min(R) forces
top2(L) < top2(R), violating the k=2 partial-sum condition of majorization.
"""
from fractions import Fraction as F
import json, sys

def matmul(X, Y):
    n, m, p = len(X), len(Y[0]), len(Y)
    return [[sum(X[i][k]*Y[k][j] for k in range(p)) for j in range(m)] for i in range(n)]

def matadd(X, Y):
    return [[X[i][j]+Y[i][j] for j in range(len(X))] for i in range(len(X))]

def matsub(X, Y):
    return [[X[i][j]-Y[i][j] for j in range(len(X))] for i in range(len(X))]

def transpose(X):
    return [list(r) for r in zip(*X)]

def eye(n): return [[F(1) if i==j else F(0) for j in range(n)] for i in range(n)]

def scale(X, s): return [[x*s for x in row] for row in X]

def diag(*d): return [[d[i] if i==j else F(0) for j in range(len(d))] for i in range(len(d))]

def is_zero(X, tol=None):
    return all(x == 0 for row in X for x in row)

def leading_minors_det(X):
    """Exact determinants of leading principal submatrices (Sylvester)."""
    n = len(X); out = []
    for k in range(1, n+1):
        S = [row[:k] for row in X[:k]]
        out.append(det(S))
    return out

def det(S):
    n = len(S)
    S = [row[:] for row in S]
    d = F(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if S[r][c] != 0), None)
        if piv is None: return F(0)
        if piv != c:
            S[c], S[piv] = S[piv], S[c]; d = -d
        d *= S[c][c]
        inv = 1/S[c][c]
        for r in range(c+1, n):
            if S[r][c] != 0:
                f = S[r][c]*inv
                for cc in range(c, n):
                    S[r][cc] -= f*S[c][cc]
    return d

def rayleigh(X, v):
    vcol = [[vi] for vi in v]           # 3x1 column
    vt = [v]                             # 1x3 row
    return (matmul(vt, matmul(X, vcol))[0][0])

R = F  # shorthand

# ---- witness from lin-rational-svd.json / lin-rational-certificate.json ----
Q = [[R(381,421), R(88,421), R(156,421)],
     [R(-72,421), R(411,421), R(-56,421)],
     [R(-164,421), R(24,421), R(387,421)]]
D = diag(R(1), R(3,5), R(0))
A = [[R(3,10), R(-111,280), R(-23,129)],
     [R(-111,280), R(3,5), R(2227,9030)],
     [R(-23,129), R(2227,9030), R(9,10)]]
B = [[R(1742720,83779), R(1127560,83779), R(0)],
     [R(1127560,83779), R(826784,83779), R(0)],
     [R(0), R(0), R(0)]]

results = {}
def check(name, ok, detail=""):
    results[name] = {"pass": bool(ok), "detail": detail}
    print(f"[{'PASS' if ok else 'FAIL'}] {name} {detail}")

# 1. Q orthogonal
check("Q_orthogonal", matmul(Q, transpose(Q)) == eye(3) and matmul(transpose(Q), Q) == eye(3))

# 2. A symmetric SPD (Sylvester: symmetric + all leading principal minors > 0)
lmA = leading_minors_det(A)
check("A_symmetric", A == transpose(A))
check("A_SPD_sylvester", all(m > 0 for m in lmA), f"leading minors = {[str(m) for m in lmA]}")

# 3. B symmetric PSD rank 2 (block diag with PSD 2x2 block, 0 last)
lmB2 = det([[B[0][0], B[0][1]],[B[1][0], B[1][1]]])
check("B_symmetric", B == transpose(B))
check("B_PSD_rank2", B[0][0] > 0 and lmB2 > 0 and B[2][2] == 0 and B[0][2]==0 and B[1][2]==0,
      f"2x2 block det = {lmB2} = {float(lmB2):.6f}")

# 4. AB = Q D and BA = D Q^T
QD = matmul(Q, D); DQt = matmul(D, transpose(Q))
AB = matmul(A, B); BA = matmul(B, A)
check("AB_equals_QD", AB == QD)
check("BA_equals_DQt", BA == DQt)

# 5. Absolute values from the DEFINITION |X| = (X* X)^{1/2}:
#    |BA| = ((BA)*(BA))^{1/2} = (A B^2 A)^{1/2}; claim = Q D Q^T (PSD, squares to A B^2 A)
ABBA = matmul(matmul(A, matmul(B, B)), A)          # A B^2 A
QDQt = matmul(Q, matmul(D, transpose(Q)))
check("abs_BA_claim_squared", matmul(QDQt, QDQt) == ABBA, "(QDQt)^2 == A B^2 A")
# PSD-ness of QDQt: eigenvalue argument — Q orthogonal, D diagonal nonneg =>
# QDQt = Q D Q^T is orthogonally similar to D, PSD. Verified structurally:
check("abs_BA_claim_PSD", True, "QDQt = Q D Q^T, Q orthogonal, D>=0 diag -> PSD (orthogonal similarity)")
#    |AB| = ((AB)*(AB))^{1/2} = (B A^2 B)^{1/2}; claim = D (PSD, squares to B A^2 B)
BAAB = matmul(matmul(B, matmul(A, A)), B)          # B A^2 B
check("abs_AB_claim_squared", matmul(D, D) == BAAB, "D^2 == B A^2 B")
check("abs_AB_claim_PSD", D[0][0] >= 0 and D[1][1] >= 0 and D[2][2] >= 0, "D diagonal nonneg")

# 6. p = 3: L = A^2 + |BA|^3 = A^2 + (QDQt)^3 = A^2 + Q D^3 Q^T ; R = A^2 + D^3
A2 = matmul(A, A)
D3 = diag(D[0][0]**3, D[1][1]**3, D[2][2]**3)
L = matadd(A2, matmul(Q, matmul(D3, transpose(Q))))
Rhs = matadd(A2, D3)
# (QDQt)^3 computed directly
cubic_QDQt = matmul(matmul(QDQt, QDQt), QDQt)
check("L_matches_direct_cube", L == matadd(A2, cubic_QDQt))
check("R_equals_A2_plus_|AB|^3", Rhs == matadd(A2, matmul(D, matmul(D, D))))

# cross-check against parent's stored L,R
parent = json.load(open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/parent-matrix-screen-r5/lin-rational-svd.json'))
def toF(m): return [[F(c) for c in row] for row in m]
check("parent_L_matches", toF(parent['L']) == L)
check("parent_R_matches", toF(parent['R']) == Rhs)

# 7. tau = 197/500
tau = R(197, 500)
Lmt = matsub(L, diag(tau, tau, tau))
lmLmt = leading_minors_det(Lmt)
check("L_minus_tauI_SPD_sylvester", all(m > 0 for m in lmLmt),
      f"leading minors = {[str(m) for m in lmLmt]}")

v = [R(-19,100), R(-1), R(37,50)]
qv = rayleigh(matsub(Rhs, diag(tau, tau, tau)), v)
check("R_rayleigh_below_tau", qv < 0, f"v^T(R-tau I)v = {qv} = {float(qv):.6e} < 0")

# 8. equal traces
trL = sum(L[i][i] for i in range(3)); trR = sum(Rhs[i][i] for i in range(3))
check("traces_equal", trL == trR, f"tr L = tr R = {trL}")

# 9. Logical conclusion: all eigenvalues of L > tau (SPD of L-tauI); R has an
#    eigenvalue < tau (Rayleigh). So lambda_min(L) > tau > lambda_min(R) =>
#    lambda_3^L > lambda_3^R; with equal traces top2(L) = tr - lam3 < tr - lam3R = top2(R).
#    Hence the k=2 partial-sum condition of lambda(L) succ lambda(R) FAILS.
# Machine corroboration of eigenvalues (mpmath 90 digits) + exact conclusion:
from mpmath import mp, mpf, eigsy
mp.dps = 90
Lf = mp.matrix([[mpq for mpq in [mp.mpf(float(x)) for x in row]] for row in L])
Rf = mp.matrix([[mpq for mpq in [mp.mpf(float(x)) for x in row]] for row in Rhs])
# NOTE: mp.mpf(float) loses precision; rebuild from exact Fraction decimal strings at 90 dps
def to_mp_matrix(M):
    out = mp.matrix(3,3)
    for i in range(3):
        for j in range(3):
            out[i,j] = mp.mpf(M[i][j].numerator) / mp.mpf(M[i][j].denominator)
    return out
Lf = to_mp_matrix(L); Rf = to_mp_matrix(Rhs)
evL_raw = [eigsy(Lf)[0][i] for i in range(3)]   # eigsy returns (w, vr); snapshot list
evL_raw = [mp.mpf(x) for x in list(eigsy(Lf)[0])]
evR_raw = [mp.mpf(x) for x in list(eigsy(Rf)[0])]
evL = sorted([float(x) for x in evL_raw], reverse=True)
evR = sorted([float(x) for x in evR_raw], reverse=True)
evL_desc_mp = sorted(evL_raw, key=lambda z: -z)
evR_desc_mp = sorted(evR_raw, key=lambda z: -z)
print("  lambda(L) desc (90dp):", [mp.nstr(x, 45) for x in evL_desc_mp])
print("  lambda(R) desc (90dp):", [mp.nstr(x, 45) for x in evR_desc_mp])
top2L = evL[0] + evL[1]; top2R = evR[0] + evR[1]
check("eigen_corroboration_L_min_above_tau", evL[2] > float(tau), f"lambda3(L)={evL[2]} > {float(tau)}")
check("eigen_corroboration_R_min_below_tau", evR[2] < float(tau), f"lambda3(R)={evR[2]} < {float(tau)}")
check("top2_L_below_top2_R", top2L < top2R, f"top2L-top2R = {top2L-top2R:.6e} < 0")

# 10. ALSO check the k=1 condition directly and the full majorization failure:
check("majorization_k2_fails", not (top2L >= top2R))
# and confirm that with equal traces this is exactly equivalent to lam3L > lam3R
check("lam3_L_gt_lam3_R", evL[2] > evR[2])

# 11. Extra adversarial checks:
# (a) Is B really PSD *singular* allowed by source? Source says "positive semidefinite"
#     (visual, p.6). YES -> rank-2 B allowed. Record only.
# (b) Would the counterexample survive if B had to be positive definite? Not required,
#     but note in review. (Skip: conjecture says semidefinite.)
# (c) Check A^2 entries vs parent JSON A2 identity: A^2 + |BA|^3 uses A^2 where A SPD.
# (d) Confirm the certificate's stored L_minus_tau_leading_minors:
cert = json.load(open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/parent-matrix-screen-r5/lin-rational-certificate.json'))
check("cert_leading_minors_match", [F(s) for s in cert['L_minus_tau_leading_minors']] == lmLmt)
check("cert_rayleigh_matches", F(cert['R_minus_tau_quadratic']) == qv)
check("cert_A_minors_match", [F(s) for s in cert['A_principal_leading_minors']] == lmA)

# (e) Verify the parent's Q is exactly the Cayley transform of its K (provenance)
K = [[0, R(1,10), R(1,5)], [R(-1,10), 0, R(-1,20)], [R(-1,5), R(1,20), 0]]
IK = matsub(eye(3), K); IKinv = []
# exact 3x3 inverse via adjugate
def inv3(M):
    d = det(M)
    cof = [[(((-1)**(i+j)) * det([[M[r][c] for c in range(3) if c!=j] for r in range(3) if r!=i])) for j in range(3)] for i in range(3)]
    return [[cof[j][i]/d for j in range(3)] for i in range(3)]  # adjugate transpose
IA = matadd(eye(3), K)
check("Q_is_cayley_of_K", matmul(inv3(IK), IA) == Q, "Q = (I-K)^{-1}(I+K)")

n_fail = sum(1 for r in results.values() if not r["pass"])
print(f"\n=== {len(results)-n_fail}/{len(results)} checks passed, {n_fail} failed ===")
json.dump({"results": results,
           "lambda_L_desc_90dp": [mp.nstr(x,45) for x in evL_desc_mp],
           "lambda_R_desc_90dp": [mp.nstr(x,45) for x in evR_desc_mp],
           "top2L_minus_top2R_float": top2L-top2R,
           "verdict": "CONJECTURE 4.3 REFUTED at p=3 (exact)" if n_fail==0 else "SEE FAILURES"},
          open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-lin-majorization-preliminary-review/review_checker_output.json','w'), indent=2)
sys.exit(1 if n_fail else 0)
