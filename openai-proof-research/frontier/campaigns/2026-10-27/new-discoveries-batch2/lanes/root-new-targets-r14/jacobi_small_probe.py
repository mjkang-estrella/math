"""Exact exploratory probe; not a source-level formal certificate."""
from pathlib import Path
import itertools
import json
import sympy as S

BASE = Path(__file__).resolve().parent
A = S.Matrix(2, 2, S.symbols('a0:4'))
B = S.Matrix(2, 2, S.symbols('b0:4'))
I = S.eye(2)
idx = list(itertools.product(range(2), repeat=4))


def operator(p, matrices, kappas):
    """Source Definition 3.5, independent matrix-entry derivatives."""
    m = 2
    c = sum(kappas) + len(kappas) * S.Rational(m, 2)
    out = 0
    for j, X in enumerate(matrices):
        for a, b, g, d in idx:
            out += (I-X)[a,d]*X[g,b]*S.diff(p,X[a,b],X[g,d])
        for a,b in itertools.product(range(m), repeat=2):
            out += ((kappas[j]+S.Rational(m,2))*I[a,b]-c*X[a,b])*S.diff(p,X[a,b])
        for l,Y in enumerate(matrices):
            if l == j:
                continue
            for a,b,g,d in idx:
                out -= S.Rational(1,2)*(X[a,d]*Y[g,b]+X[g,b]*Y[a,d])*S.diff(p,X[a,b],Y[g,d])
    return S.expand(out)


def main():
    # The monic one-matrix P_(1,1) for (kappa1,kappa2)=(1,1).
    single = B.det()-S.trace(B)/2+S.Rational(1,3)
    checks = {'single_P11_eigen_residual': str(operator(single,[B],[1,1])+6*single)}
    checks['single_P11_eigen_residual'] = str(S.expand(S.sympify(checks['single_P11_eigen_residual'])))
    C = I-A
    Q = S.expand(B.det()-S.trace(B*C.adjugate())/2+C.det()/3)
    GQ = operator(Q,[A,B],[1,1,1])
    checks['P0_P11_residual'] = str(S.expand(GQ+10*Q))
    # Source equation (21) gives a1=2+1+1=4, hence tr(A)-4/7.
    # Its beta marginal shift is the suspected issue; test both constants.
    for den in [7,8]:
        P = S.expand((S.trace(A)-S.Rational(4,den))*Q)
        GP = operator(P,[A,B],[1,1,1])
        terms = S.Poly(P,*(list(A)+list(B))).terms()
        mon, coeff = max(terms,key=lambda item:sum(item[0]))
        eigen = S.Poly(GP,*(list(A)+list(B))).coeff_monomial(mon)/coeff
        residual = S.factor(GP-eigen*P)
        checks[f'denominator_{den}'] = {'eigenvalue_from_top':str(eigen),'residual':str(residual),
            'residual_divided_by_Q':str(S.cancel(residual/Q))}
    (BASE/'jacobi-small-probe.json').write_text(json.dumps(checks,indent=2)+'\n')
    print(json.dumps(checks,indent=2))


if __name__ == '__main__':
    main()
