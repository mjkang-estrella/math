"""Five preregistered exact cases. No randomness, timing or parameter search."""
from fractions import Fraction as F
from math import factorial, gcd
from pathlib import Path
import datetime
import hashlib
import json
import traceback

ROOT = Path(__file__).resolve().parents[2]
PREFIX = ROOT / 'research/findings/W014-integer-valued-review'


def choose(x, k):
    value = F(1)
    for j in range(k):
        value *= F(x-j, j+1)
    return value


def transfer():
    N, p, X, q, M, alpha = 15, 3, 2, 1, 2, 2
    A = lambda h: choose(h, 2)
    e, D = A(p-X)-q*(N//p), A(1-X)-q*N
    beta = pow(alpha, M, N)
    coeff = [-30, 16, -5, 1]
    value = sum(c*p**j for j, c in enumerate(coeff))
    checks = {
        'negative_offset_integral': A(1-X) == 1,
        'e_and_D_integral': e.denominator == D.denominator == 1,
        'unit': gcd(alpha, N) == 1,
        'cleared_congruence': (M*(D-e)) % (p-1) == 0,
        'uncleared_congruence_fails': (D-e) % (p-1) != 0,
        'powered_equality': pow(beta, int(D), p) == pow(beta, int(e), p),
        'unpowered_equality_fails': pow(alpha, int(D), p) != pow(alpha, int(e), p),
        'recovery_coefficients_exact': coeff == [-M*q*N, 6-M*int(e), -5, 1],
        'true_root': value == 0,
        'nonzero_constant': coeff[0] != 0,
    }
    return {'parameters': {'N': N, 'p': p, 'X': X, 'q': q, 'M': M, 'alpha': alpha},
            'A_negative_offset': str(A(1-X)), 'e': str(e), 'D': str(D),
            'M_times_D_minus_e': str(M*(D-e)), 'beta_mod_N': beta,
            'alpha_powers_mod_p': [pow(alpha, int(D), p), pow(alpha, int(e), p)],
            'beta_powers_mod_p': [pow(beta, int(D), p), pow(beta, int(e), p)],
            'recovery_coefficients_ascending': coeff, 'F_at_p': value,
            'checks': checks}


def order_loss():
    N, alpha = 15, 2
    beta2, beta24 = pow(alpha, 2, N), pow(alpha, factorial(4), N)
    checks = {
        'alpha_order_4': pow(alpha, 1, N) != 1 and pow(alpha, 2, N) != 1 and pow(alpha, 4, N) == 1,
        'M2_beta_order_2': beta2 != 1 and pow(beta2, 2, N) == 1,
        'M24_beta_order_1': beta24 == 1,
    }
    return {'N': N, 'alpha': alpha, 'alpha_powers_1_2_4': [pow(alpha, k, N) for k in (1, 2, 4)],
            'M2_beta': beta2, 'M24_beta': beta24, 'checks': checks}


def grid_case(kind):
    X, N, q, L = 10**6, 10**12, 1, 8
    if kind == 'dense_affine':
        d, E = 2, F(64, X)
        A = lambda h: F(X-h)
    elif kind == 'drop_integrality':
        d, E = 2, F(512, X**2)
        A = lambda h: F(X-h)+F(h*h, X)
    elif kind == 'drop_density':
        d, E = 9, F(64, X)
        A = lambda h: F(X-h)+choose(h, 9)
    else:
        raise ValueError(kind)
    vals = [A(j) for j in range(L+1)]
    errors = [vals[j]-F(q*N, X+j) for j in range(L+1)]
    diffs = [vals[j+2]-2*vals[j+1]+vals[j] for j in range(L-1)]
    lhs = 8*d**4*(E/L**2+F(q*N, X**3))
    integral = all(v.denominator == 1 for v in vals)
    dense = L >= 2*d*d
    checks = {'uniform_error': all(abs(v) <= E for v in errors), 'A1': lhs < 1}
    if kind == 'dense_affine':
        checks.update(density=dense, grid_integrality=integral, second_differences_zero=all(v == 0 for v in diffs))
    elif kind == 'drop_integrality':
        checks.update(density=dense, grid_integrality_fails=not integral,
                      nonaffine=all(v == F(2, X) for v in diffs))
    else:
        checks.update(density_fails=not dense, grid_integrality=integral,
                      second_differences_zero_on_grid=all(v == 0 for v in diffs),
                      nonaffine_outside_grid=A(9) != X-9,
                      actual_degree_nine=choose(9, 9) == 1)
    return {'parameters': {'X': X, 'N': N, 'q': q, 'L': L, 'd': d, 'E': str(E)},
            'grid': [{'j': j, 'A': str(vals[j]), 'error': str(errors[j])} for j in range(L+1)],
            'second_differences': list(map(str, diffs)), 'A1_lhs': str(lhs),
            'density_guard': dense, 'grid_integrality': integral, 'A_at_9': str(A(9)),
            'checks': checks}


if __name__ == '__main__':
    output = Path(str(PREFIX)+'-certificate-output.json')
    if output.exists():
        raise SystemExit('Refusing to overwrite retained results or rerun the certificate.')
    cases = [('transfer', transfer), ('order_loss', order_loss),
             ('dense_affine', lambda: grid_case('dense_affine')),
             ('drop_integrality', lambda: grid_case('drop_integrality')),
             ('drop_density', lambda: grid_case('drop_density'))]
    result = {'started_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'brief_sha256': hashlib.sha256(Path(str(PREFIX)+'-certificate-brief.md').read_bytes()).hexdigest(),
              'cases': [], 'verified_complete_factoring_improvement': 'NONE'}
    for name, fn in cases:
        try:
            row = fn()
            row.update(name=name, status='pass' if all(row['checks'].values()) else 'fail')
        except Exception:
            row = {'name': name, 'status': 'error', 'traceback': traceback.format_exc()}
        result['cases'].append(row)
    result['passed'] = sum(row['status'] == 'pass' for row in result['cases'])
    result['total'] = len(cases)
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'passed': result['passed'], 'total': result['total'], 'output': str(output)}))
    raise SystemExit(0 if result['passed'] == result['total'] else 1)
