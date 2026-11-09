"""Inspect g_n (n = 2 mod 3) of the three-shifted q-Motzkin Hankel determinants: print g_n and test
divisibility by cyclotomic polynomials Phi_d (d <= 40) and by t_m for nearby m (read-only diagnostics)."""
import importlib.util
import json
import sys

spec = importlib.util.spec_from_file_location('qm', sys.argv[1])
Q = importlib.util.module_from_spec(spec)
spec.loader.exec_module(Q)
ns = [int(x) for x in sys.argv[2].split(',')]


def cyclotomic(d):
    # Phi_d = (q^d - 1) / prod_{e|d, e<d} Phi_e
    num = [-1] + [0] * (d - 1) + [1]
    for e in range(1, d):
        if d % e == 0:
            num = Q.divexact(num, cyclotomic(e))
    return num


def mult(p, f):
    k = 0
    while True:
        qq, r = Q.divmod_poly(p, f)
        if qq is None or r:
            return k
        p = qq
        k += 1


def t(m):
    p = [0] * (3 * (m // 3) + 1)
    for k in range(m // 3 + 1):
        p[3 * k] = 1
    return p


for n in ns:
    d = Q.block_det(n, 3)
    c = next(i for i, x in enumerate(d) if x)
    g = d[c:]
    if g[-1] < 0:
        g = [-x for x in g]
    cyc = {dd: mult(g, cyclotomic(dd)) for dd in range(1, 41)}
    cyc = {k: v for k, v in cyc.items() if v}
    tdiv = {m: (Q.divmod_poly(g, t(m))[1] == []) for m in range(1, n + 4)}
    rem = Q.divmod_poly(g, t(n))
    print(json.dumps({'n': n, 'c_n': c, 'g_n': g if len(g) < 80 else 'deg %d' % (len(g) - 1),
                      'g(1)': sum(g), 'cyclotomic_multiplicities': cyc,
                      't_m_divides': [m for m, v in tdiv.items() if v], 't_n': t(n),
                      'remainder_mod_t_n': rem[1]}))
