"""Exact symbolic check (in Z[zeta_e][t], zeta_e a formal primitive e-th root, i.e. modulo Phi_e) of the
claims of 338887-proof.md Steps 4-5 for every e in 1..EMAX:
  (a) P := X_0 X_1 ... X_{e-1}, X_k = [[1+z, -z g_k], [g_k, 0]], g_k = 1 - t z^k, has
      Tr P = 2 + q_e t^e with q_e = 0 (e odd), 2 (4|e), -2 (e = 2 mod 4);
  (b) det P = (1 - t^e)^2;
  (c) prod_{k<e} (1 - t z^k) = 1 - t^e;
  (d) the t-coefficient matrix of X_k is z^k J, J = [[0, z], [-1, 0]], and J^2 = -z I.
Working modulo Phi_e covers every primitive e-th root simultaneously (Galois conjugates).
Usage: python3 -I trace_sym.py EMAX
"""
import json
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cyclo import Cyc, tp_add, tp_sub, tp_mul, tp_trim  # noqa: E402


def qe(e):
    if e % 2 == 1:
        return 0
    return 2 if e % 4 == 0 else -2


def check(e):
    C = lambda a: Cyc.const(e, a)
    Z = lambda k: Cyc.zpow(e, k)
    one_plus_z = C(1) + Z(1)
    def X(k):
        g = [C(1), -Z(k)]                      # 1 - t z^k
        mzg = [-Z(1), Z(1) * Z(k)]             # -z g_k = -z + t z^{k+1}
        return [[[one_plus_z], mzg], [g, []]]
    def mm(A, B):
        return [[tp_trim(tp_add(tp_mul(A[i][0], B[0][j], e), tp_mul(A[i][1], B[1][j], e), e)) for j in range(2)]
                for i in range(2)]
    P = X(0)
    for k in range(1, e):
        P = mm(P, X(k))
    tr = tp_trim(tp_add(P[0][0], P[1][1], e))
    det = tp_trim(tp_sub(tp_mul(P[0][0], P[1][1], e), tp_mul(P[0][1], P[1][0], e), e))
    expect_tr = [C(0)] * (e + 1)
    expect_tr[0] = C(2)
    expect_tr[e] = expect_tr[e] + C(qe(e))
    expect_tr = tp_trim(expect_tr)
    expect_det = [C(0)] * (2 * e + 1)
    expect_det[0] = C(1)
    expect_det[e] = C(-2)
    expect_det[2 * e] = C(1)
    expect_det = tp_trim(expect_det)
    prod = [C(1)]
    for k in range(e):
        prod = tp_mul(prod, [C(1), -Z(k)], e)
    prod = tp_trim(prod)
    expect_prod = [C(0)] * (e + 1)
    expect_prod[0] = C(1)
    expect_prod[e] = expect_prod[e] + C(-1)
    expect_prod = tp_trim(expect_prod)
    # (d): t-coefficient of X_k
    d_ok = True
    J = [[C(0), Z(1)], [C(-1), C(0)]]
    for k in range(e):
        Xk = X(k)
        t1 = [[(Xk[i][j][1] if len(Xk[i][j]) > 1 else C(0)) for j in range(2)] for i in range(2)]
        if any(not (t1[i][j] == Z(k) * J[i][j]) for i in range(2) for j in range(2)):
            d_ok = False
    J2 = [[J[i][0] * J[0][j] + J[i][1] * J[1][j] for j in range(2)] for i in range(2)]
    d_ok = d_ok and J2[0][0] == -Z(1) and J2[1][1] == -Z(1) and J2[0][1].is_zero() and J2[1][0].is_zero()
    tr_int = [c.as_int() for c in tr]
    return {"e": e, "trace_coeffs": tr_int, "q_e": qe(e),
            "trace_ok": tr == expect_tr, "det_ok": det == expect_det, "prod_ok": prod == expect_prod,
            "tcoef_J_ok": d_ok}


def main():
    emax = int(sys.argv[1])
    allok = True
    rows = []
    for e in range(1, emax + 1):
        r = check(e)
        rows.append(r)
        ok = r["trace_ok"] and r["det_ok"] and r["prod_ok"] and r["tcoef_J_ok"]
        allok &= ok
        print(json.dumps(r), flush=True)
    print(json.dumps({"emax": emax, "all_ok": allok}))


if __name__ == "__main__":
    main()
