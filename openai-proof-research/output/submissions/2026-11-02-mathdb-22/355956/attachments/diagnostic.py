"""Independent exact diagnostic for MathDB 355956 (q = 5^8, d = 3).

Standard library only; arithmetic in F_5[X]/(f), f = X^8 + X^7 + 2X^6 + 2.
The certificate polynomials (Frobenius chain, cube roots, inverses) are parsed
from the literal Lean module proof/Yip355956.lean and rechecked here with
independent code.  Everything printed is corroboration, never a premise of
the Lean theorem.  Output: replay-receipts/diagnostic.json (or argv[1]).
"""
import json, pathlib, re, sys, time

P, N = 5, 8
Q = P ** N
F = [2, 0, 0, 0, 0, 0, 2, 1, 1]          # coefficients of f, low degree first
ROOT = pathlib.Path(__file__).resolve().parent
LEAN = ROOT / 'proof' / 'Yip355956.lean'


def norm(a):
    a = [c % P for c in a]
    while a and a[-1] == 0:
        a.pop()
    return a


def pmod(a, m):
    a = norm(a)
    m = norm(m)
    inv = pow(m[-1], P - 2, P)
    while len(a) >= len(m):
        c = a[-1] * inv % P
        s = len(a) - len(m)
        for i, mc in enumerate(m):
            a[s + i] = (a[s + i] - c * mc) % P
        a = norm(a)
    return a


def pmul(a, b):
    r = [0] * (len(a) + len(b) + 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return norm(r)


def mulf(a, b):
    return pmod(pmul(a, b), F)


def powf(a, e):
    r, b = [1], pmod(a, F)
    while e:
        if e & 1:
            r = mulf(r, b)
        b = mulf(b, b)
        e >>= 1
    return r


def sub(a, b):
    n = max(len(a), len(b))
    return norm([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])


def pgcd(a, b):
    a, b = norm(a), norm(b)
    while b:
        a, b = b, pmod(a, b)
    inv = pow(a[-1], P - 2, P)
    return norm([c * inv for c in a])


def parse_poly(s, var):
    """Parse a Lean polynomial like '(2) * 1 + (3) * t + (4) * t^5' into coefficients."""
    out = [0] * 8
    for coef, mono in re.findall(r'\((-?\d+)\)\s*\*\s*(1|%s(?:\^\d+)?)' % var, s):
        k = 0 if mono == '1' else (int(mono.split('^')[1]) if '^' in mono else 1)
        out[k] += int(coef)
    return norm(out)


def lean_certificates(text):
    chain = {}
    for k, rhs in re.findall(r'have h(\d) : t \^ \(5 \^ \d\) = (.*?) := by', text):
        chain[int(k)] = parse_poly(rhs, 't')
    cubes, invs = {}, {}
    for a, base in re.findall(r'theorem cube_(\d) .*?\n\s+\((.*?)\) \^ 3 = wit', text, re.S):
        cubes[int(a)] = parse_poly(base, 'θ')
    for a, h in re.findall(r'theorem inv_(\d) .*?\n\s+\(wit θ - \d\) \* \((.*?)\) = 1', text, re.S):
        invs[int(a)] = parse_poly(h, 'θ')
    return chain, cubes, invs


def main(out_path):
    t0 = time.time()
    r = {'q': Q, 'd': 3, 'f_low_to_high': F}
    r['q_minus_1'] = Q - 1
    r['q_mod_6'] = Q % 6
    adm = [k for k in range(1, 30) if P ** k - 1 <= Q - 1 and (Q - 1) % (P ** k - 1) == 0
           and ((Q - 1) // (P ** k - 1)) % 3 == 0]
    r['integral_quotients'] = {k: (Q - 1) // (P ** k - 1) for k in range(1, 9) if (Q - 1) % (P ** k - 1) == 0}
    r['admissible_r'] = adm
    # Frobenius (Berlekamp) matrix rows X^(5i) mod f, i = 0..7.
    X = [0, 1]
    rows = [powf(X, 5 * i) for i in range(8)]
    r['frobenius_rows_X^5i_mod_f'] = rows
    chain = [X]
    for _ in range(8):
        cur = chain[-1]
        nxt = []
        for i, c in enumerate(cur):          # P(X)^5 = sum c_i X^(5i) in characteristic 5
            nxt = sub(nxt, [(-c * v) for v in rows[i]])
        chain.append(norm(nxt))
    r['frobenius_chain_P_k'] = chain
    r['chain_matches_square_and_multiply'] = all(chain[k] == powf(X, 5 ** k) for k in range(9))
    r['X^(5^8) = X'] = chain[8] == X
    r['P_k_ne_X_for_k_1_to_7'] = all(chain[k] != X for k in range(1, 8))
    r['gcd_f_P4_minus_X'] = pgcd(F, sub(chain[4], X))
    r['f_irreducible'] = r['X^(5^8) = X'] and chain[4] != X and r['gcd_f_P4_minus_X'] == [1]
    text = LEAN.read_text(encoding='utf-8')
    lchain, cubes, invs = lean_certificates(text)
    r['lean_chain_parsed'] = sorted(lchain)
    r['lean_chain_matches'] = all(lchain.get(k) == chain[k] for k in range(1, 9))
    x = [0, 2, 4, 1]
    r['x_low_to_high'] = x
    r['cube_roots_y_a'] = {a: cubes[a] for a in sorted(cubes)}
    r['inverses_h_a'] = {a: invs[a] for a in sorted(invs)}
    e3 = (Q - 1) // 3
    checks = {}
    for a in range(5):
        xa = sub(x, [a])
        checks[a] = {
            'y_a^3 == x-a': powf(cubes[a], 3) == xa,
            '(x-a)*h_a == 1': mulf(xa, invs[a]) == [1],
            '(x-a)^((q-1)/3) == 1': powf(xa, e3) == [1],
        }
    r['per_a_checks'] = checks
    r['minus_one_is_cube'] = powf([P - 1], e3) == [1]
    r['F5_star_cubes'] = all(powf([a], e3) == [1] for a in range(1, 5))
    r['x^5 != x'] = powf(x, 5) != x
    span = [sub([a], [(-b * c) for c in x]) for a in range(5) for b in range(5)]   # a + b x
    r['F5+xF5_nonzero_all_cubes'] = all(powf(v, e3) == [1] for v in span if v)
    r['F5+xF5_size'] = len({tuple(v) for v in span})
    # Primitive element and subfield clique tests.
    fac = [2, 3, 13, 313]
    r['q_minus_1_factorisation'] = '2^5 * 3 * 13 * 313'
    assert 2 ** 5 * 3 * 13 * 313 == Q - 1
    r['X_primitive'] = all(powf(X, (Q - 1) // l) != [1] for l in fac)
    for k in (2, 4):
        g = powf(X, (Q - 1) // (P ** k - 1))
        r['F_%d_generator_is_cube' % P ** k] = powf(g, e3) == [1]
    # Exhaustive count of extension vertices via a discrete-log table of X.
    def code(v):
        return sum(c * P ** i for i, c in enumerate(v))
    log = [-1] * Q
    cur = [1] + [0] * 7
    for e in range(Q - 1):
        c = sum(cur[i] * P ** i for i in range(8))
        if log[c] != -1:
            raise SystemExit('X is not primitive')
        log[c] = e
        top = cur[7]
        cur = [0] + cur[:7]
        if top:
            for i in range(8):
                cur[i] = (cur[i] - top * F[i]) % P
    r['log_table_covers_all_nonzero'] = sum(1 for v in log[1:] if v >= 0) == Q - 1
    cube = [v >= 0 and v % 3 == 0 for v in log]
    ext = []
    for c in range(Q):
        c0 = c % P
        if c < P:
            continue
        if all(cube[c - c0 + (c0 - a) % P] for a in range(P)):
            ext.append(c)
    r['extension_vertices'] = len(ext)
    r['x_is_extension_vertex'] = code(x) in set(ext)
    in625 = [c for c in ext if log[c] % 626 == 0]
    r['extension_vertices_in_F625'] = len(in625)
    r['seconds'] = round(time.time() - t0, 2)
    ok = (adm == [1] and r['chain_matches_square_and_multiply'] and r['f_irreducible'] and r['lean_chain_matches']
          and all(all(v.values()) for v in checks.values()) and r['minus_one_is_cube'] and r['F5_star_cubes']
          and r['x^5 != x'] and r['F5+xF5_nonzero_all_cubes'] and r['F5+xF5_size'] == 25 and r['X_primitive']
          and not r['F_25_generator_is_cube'] and not r['F_625_generator_is_cube'] and r['log_table_covers_all_nonzero']
          and r['x_is_extension_vertex'] and len(cubes) == 5 and len(invs) == 5)
    r['status'] = 'PASS' if ok else 'FAIL'
    pathlib.Path(out_path).parent.mkdir(exist_ok=True)
    pathlib.Path(out_path).write_text(json.dumps(r, indent=1, default=str))
    print(r['status'], 'admissible', adm, 'extension vertices', r['extension_vertices'], 'in F625', len(in625), r['seconds'], 's')
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1] if len(sys.argv) > 1 else str(ROOT / 'replay-receipts' / 'diagnostic.json')) else 1)
