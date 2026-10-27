#!/usr/bin/env python3
"""Independent exact verification of the PRIOR ART witness from
the-omega-institute/trureturing (D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation):
A = diag(3,1,1/2), B = [[1/2,1/4,3/4],[1/4,3/4,0],[3/4,0,5/2]], p = 4, tau = 7/5.
Mechanism: L = A^2+|BA|^4 satisfies L - (7/5)I PSD; v=(0,-1,19/64) gives
v^T(R-(7/5)I)v < 0 for R = A^2+|AB|^4; equal traces -> two-prefix violation.
"""
from fractions import Fraction as F
import json

def matmul(X, Y):
    return [[sum(X[i][k]*Y[k][j] for k in range(len(Y))) for j in range(len(Y[0]))] for i in range(len(X))]
def matsub(X, Y): return [[x-y for x, y in zip(r1, r2)] for r1, r2 in zip(X, Y)]
def eye(n): return [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]

def det(S):
    n = len(S); S = [r[:] for r in S]; d = F(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if S[r][c] != 0), None)
        if piv is None: return F(0)
        if piv != c: S[c], S[piv] = S[piv], S[c]; d = -d
        d *= S[c][c]
        for r in range(c+1, n):
            if S[r][c] != 0:
                f = S[r][c]/S[c][c]
                for cc in range(c, n): S[r][cc] -= f*S[c][cc]
    return d

def principal_minors(X):
    n = len(X); out = []
    for size in range(1, n+1):
        for rows in __import__('itertools').combinations(range(n), size):
            out.append(det([[X[i][j] for j in rows] for i in rows]))
    return out

R = F
A = [[R(3), 0, 0], [0, R(1), 0], [0, 0, R(1, 2)]]
B = [[R(1,2), R(1,4), R(3,4)], [R(1,4), R(3,4), R(0)], [R(3,4), R(0), R(5,2)]]
tau = R(7, 5)
v = [R(0), R(-1), R(19, 64)]

res = {}
A2 = matmul(A, A)
AB2A = matmul(matmul(A, matmul(B, B)), A)      # A B^2 A = (|BA|)^2
BA2B = matmul(matmul(B, matmul(A, A)), B)      # B A^2 B = (|AB|)^2
L = [[a+b for a, b in zip(r1, r2)] for r1, r2 in zip(A2, matmul(AB2A, AB2A))]  # A^2+|BA|^4 = A^2+(AB^2A)^2
Rm = [[a+b for a, b in zip(r1, r2)] for r1, r2 in zip(A2, matmul(BA2B, BA2B))]          # A^2+|AB|^4

# B PSD: all principal minors >= 0
pmB = principal_minors(B)
res['B_PSD_all_principal_minors'] = all(m >= 0 for m in pmB)
res['B_principal_minors'] = [str(m) for m in pmB]

# L - tau I PSD: all principal minors >= 0
Lmt = matsub(L, [[tau if i == j else 0 for j in range(3)] for i in range(3)])
pmL = principal_minors(Lmt)
res['L_minus_tauI_PSD_all_principal_minors'] = all(m >= 0 for m in pmL)
res['L_minus_tauI_principal_minors'] = [str(m) for m in pmL]

# v^T (R - tau I) v < 0
Rmt = matsub(Rm, [[tau if i == j else 0 for j in range(3)] for i in range(3)])
qv = sum(v[i]*Rmt[i][j]*v[j] for i in range(3) for j in range(3))
res['v_Rmt_v'] = str(qv)
res['v_Rmt_v_negative'] = qv < 0

# traces equal
res['traces_equal'] = sum(L[i][i] for i in range(3)) == sum(Rm[i][i] for i in range(3))
res['trace'] = str(sum(L[i][i] for i in range(3)))

# 90-digit eigenvalues
from mpmath import mp, eigsy
mp.dps = 90
def to_mp(M):
    out = mp.matrix(3, 3)
    for i in range(3):
        for j in range(3):
            out[i, j] = mp.mpf(M[i][j].numerator)/mp.mpf(M[i][j].denominator)
    return out
evL = sorted([mp.mpf(x) for x in list(eigsy(to_mp(L))[0])], key=lambda z: -z)
evR = sorted([mp.mpf(x) for x in list(eigsy(to_mp(Rm))[0])], key=lambda z: -z)
res['lambda_L_desc'] = [mp.nstr(x, 45) for x in evL]
res['lambda_R_desc'] = [mp.nstr(x, 45) for x in evR]
res['lambda3_L_ge_tau'] = evL[2] >= mp.mpf(tau.numerator)/mp.mpf(tau.denominator)
res['lambda3_R_lt_tau'] = evR[2] < mp.mpf(tau.numerator)/mp.mpf(tau.denominator)
res['top2_violation'] = (evL[0]+evL[1]) < (evR[0]+evR[1])
res['top2_diff'] = mp.nstr((evL[0]+evL[1])-(evR[0]+evR[1]), 30)

ok = (res['B_PSD_all_principal_minors'] and res['L_minus_tauI_PSD_all_principal_minors']
      and res['v_Rmt_v_negative'] and res['traces_equal'] and res['lambda3_L_ge_tau']
      and res['lambda3_R_lt_tau'] and res['top2_violation'])
res['VERDICT'] = 'PRIOR-ART WITNESS CONFIRMED: Conjecture 4.3 refuted at p=4 exactly' if ok else 'MISMATCH - inspect'
print(json.dumps(res, indent=2))
json.dump(res, open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-lin-majorization-preliminary-review/prior_art_witness_check.json', 'w'), indent=2)
