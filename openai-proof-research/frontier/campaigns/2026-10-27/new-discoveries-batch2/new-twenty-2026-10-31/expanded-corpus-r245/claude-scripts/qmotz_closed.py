"""Data-driven closed forms for g_n of the three-shifted q-Motzkin Hankel determinants (diagnostic):
split g_n(q) = A(q^3) + q B(q^3) + q^2 C(q^3) and test
  n = 3m+1 : g = (1+q)^2 t^2                        (source claim)
  n = 3m+2 : A = t^2, B = 2 E(x) F(x), C = 0, E = sum_{k<=m//2} x^{2k}, F = sum_{j<=2*ceil(m/2)} x^j
  n = 3m   : A = (sum_{k<=m} x^k)^2, B = 0, and print C/2
where t = sum_{k<=m} x^k (x = q^3)."""
import importlib.util
import json
import sys

spec = importlib.util.spec_from_file_location('qm', sys.argv[1])
Q = importlib.util.module_from_spec(spec)
spec.loader.exec_module(Q)
NMAX = int(sys.argv[2])


def ones(k):
    return [1] * (k + 1)


def spread(p, step, off=0):
    r = [0] * (step * (len(p) - 1) + 1 + off) if p else []
    for i, x in enumerate(p):
        r[off + step * i] += x
    return Q.trim(r)


res = {}
for n in range(1, NMAX + 1):
    d = Q.block_det(n, 3)
    c = next(i for i, x in enumerate(d) if x)
    g = d[c:]
    if g[-1] < 0:
        g = [-x for x in g]
    A = Q.trim([g[i] for i in range(0, len(g), 3)])
    B = Q.trim([g[i] for i in range(1, len(g), 3)])
    C = Q.trim([g[i] for i in range(2, len(g), 3)])
    m = n // 3
    t = ones(m)
    if n % 3 == 1:
        ok = (g == Q.mul(Q.mul([1, 1], [1, 1]), Q.mul(spread(t, 3), spread(t, 3))))
        res[n] = {'rule': 'n=3m+1 source formula', 'ok': ok}
    elif n % 3 == 2:
        E = spread(ones(m // 2), 2)
        F = ones(2 * ((m + 1) // 2))
        ok = (A == Q.mul(t, t)) and (B == Q.mul([2], Q.mul(E, F))) and C == []
        res[n] = {'rule': 'n=3m+2 guessed closed form', 'ok': ok}
    else:
        ok = (A == Q.mul(ones(m), ones(m))) and B == []
        half = [x // 2 for x in C] if all(x % 2 == 0 for x in C) else C
        res[n] = {'rule': 'n=3m A=(1+..+x^m)^2, B=0', 'ok': ok, 'C_over_2': half, 'c_n': c}
    print(n, json.dumps(res[n]), flush=True)
print('ALL_OK', all(v['ok'] for v in res.values()))
