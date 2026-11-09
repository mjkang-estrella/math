"""Fixed exact W014 B certificate; see preregistration.md. No solver imports."""
from fractions import Fraction
from math import comb, factorial, gcd
import json
import sys
import traceback


RESULTS = []


def poly(coeffs, x):
    total = 0
    for a in reversed(coeffs):
        total = total * x + a
    return total


def image(coeffs, modulus, domain=None):
    return sorted({poly(coeffs, x) % modulus
                   for x in (range(modulus) if domain is None else domain)})


def valuation(n, prime):
    if n == 0:
        return None  # Infinity, never a finite derivative witness.
    n = abs(n)
    result = 0
    while n % prime == 0:
        n //= prime
        result += 1
    return result


def normalize(coeffs, modulus):
    common = gcd(modulus, *coeffs[1:])
    r0 = coeffs[0] % common
    return common, modulus // common, r0, [
        (coeffs[0] - r0) // common,
        *(a // common for a in coeffs[1:]),
    ]


def check(case, name, actual, expected):
    case['checks'].append(dict(name=name, actual=actual, expected=expected,
                               passed=actual == expected))


def exact_order(case, base, modulus, expected, name):
    values = [pow(base, j, modulus) for j in range(1, expected + 1)]
    case['details'][name + '_powers'] = values
    check(case, name, values.index(1) + 1 if 1 in values else None, expected)


def case1(c):
    a = [-13, 0, 18]
    g, m, r, q = normalize(a, 12)
    check(c, 'normalization', [g, m, r, q], [6, 2, 5, [-3, 0, 3]])
    rows = []
    for h in [-3, -1, 0, 1, 2, 3]:
        pval, qval = poly(a, h), poly(q, h)
        rows.append([h, pval, qval, pval // 12, qval // m, pval % 12])
        check(c, 'floor_' + str(h), pval // 12, qval // m)
        check(c, 'remainder_' + str(h), pval % 12, r + g * (qval % m))
    c['details']['offsets'] = rows
    check(c, 'image_bijection', image(a, 12), [r + g * x for x in image(q, m)])
    check(c, 'image', image(a, 12), [5, 11])
    check(c, 'constant', list(normalize([-13, 0, 0], 12)),
          [12, 1, 11, [-2, 0, 0]])
    check(c, 'constant_negative_floor', -13 // 12, -2)


def case2(c):
    q = [0, 0, 1, 0, 1]
    derivatives = [4*x**3 + 2*x for x in range(4)]
    vals = [valuation(v, 2) for v in derivatives]
    c['details'].update(derivatives=derivatives, valuations=vals)
    check(c, 's_max', 2 + valuation(factorial(3), 2), 3)
    check(c, 'chosen_s', vals[1], 1)
    # Coefficients of Q(1+4t)-Q(1), formed by exact binomial expansion.
    expanded = [sum(a * comb(j, k) * 4**k for j, a in enumerate(q) if j >= k)
                for k in range(5)]
    expanded[0] -= poly(q, 1)
    check(c, 'Taylor_coefficients', expanded, [0, 24, 112, 256, 256])
    check(c, 'divided_Taylor', [v // 8 for v in expanded], [0, 3, 14, 32, 32])
    hvals = [(3*t + 2*(7*t*t + 16*t**3 + 16*t**4)) % 8 for t in range(8)]
    c['details']['local_map_values_mod_8'] = hvals
    check(c, 'local_bijection', sorted(hvals), list(range(8)))
    coset = list(range(2, 64, 8))
    obtained = sorted({poly(q, 1 + 4*t) % 64 for t in range(8)})
    check(c, 'Taylor_coset', obtained, coset)
    full = image(q, 64)
    c['details']['full_image_mod_64'] = full
    check(c, 'coset_containment', set(coset).issubset(full), True)
    check(c, 'small_prime_bound', len(full)*2**7 >= 64, True)


def case3(c):
    q = [0, -1, 0, 1]
    check(c, 'primitive', gcd(3, *q[1:]), 1)
    check(c, 'constant_function_mod_3', image(q, 3), [0])
    check(c, 'derivative_at_zero', -1, -1)
    check(c, 'derivative_valuation', valuation(-1, 3), 0)
    check(c, 'image_mod_27', image(q, 27), list(range(0, 27, 3)))
    c['details']['Taylor_coefficients_Q_3t'] = [0, -3, 0, 27]


def case4(c):
    regular = [x for x in range(7) if 2*x % 7]
    regular_values = sorted({x*x % 7 for x in regular})
    check(c, 'regular_values', regular_values, [1, 2, 4])
    full = image([0, 0, 1], 49)
    c['details'].update(regular_preimages=regular, full_image=full)
    for value in regular_values:
        check(c, 'all_lifts_' + str(value),
              [x for x in full if x % 7 == value],
              [value + 7*t for t in range(7)])
    check(c, 'image_size', len(full), 22)
    check(c, 'strong_lower_bound', 2*len(full) >= 7*(7-2+1), True)
    check(c, 'weak_lower_bound', 4*len(full) >= 49, True)


def case5(c):
    q = [0, 0, 1]
    i8, i9, i72 = image(q, 8), image(q, 9), image(q, 72)
    actual = sorted((x % 8, x % 9) for x in i72)
    expected = sorted((a, b) for a in i8 for b in i9)
    c['details'].update(image8=i8, image9=i9, image72=i72)
    check(c, 'CRT_product', actual, expected)
    check(c, 'cardinalities', [len(i8), len(i9), len(i72)], [3, 4, 12])
    cd = 2**3 * 3
    check(c, 'C_2', cd, 24)
    check(c, 'global_bound', len(i72)*cd*4**2 >= 72, True)
    check(c, 'naive_composite_M_over_d_fails', len(i72) < 72//2, True)


def case6(c):
    n, alpha, m, x, q, emax, b = 35, 2, 2, 5, 1, 1, 2
    coeffs = [15, -2]
    beta = pow(alpha, m, n)
    check(c, 'unit', gcd(alpha, n), 1)
    exact_order(c, beta, n, 6, 'global_order')
    check(c, 'component_gcd', gcd(beta-1, n), 1)
    e, r = poly(coeffs, 0)//m - q*(n//5), poly(coeffs, 0) % m
    d = poly(coeffs, 1-x) - m*q*n
    check(c, 'error_remainder_D', [e, r, d], [0, 1, -47])
    check(c, 'transfer', (d-m*e-r) % 4, 0)
    babies = [pow(beta, j, n) for j in range(b)]
    rows = []
    for k in range((2*emax+1+b-1)//b):
        exponent = d-r+m*emax-m*k*b
        giant = pow(alpha, exponent, n)
        rows.append(dict(k=k, exponent=exponent, giant=giant,
                         errors=[k*b+j-emax for j in range(b)],
                         global_babies=[j for j, y in enumerate(babies) if y == giant]))
    c['details'].update(babies=babies, giants=rows)
    check(c, 'true_indices', list(divmod(e+emax, b)), [0, 1])
    check(c, 'true_exponent', rows[0]['exponent'], -46)
    check(c, 'true_global_baby', rows[0]['global_babies'], [1])
    check(c, 'padding', rows[1]['errors'], [1, 2])
    recovery = [-m*q*n, coeffs[0]-coeffs[1]*x-r-m*e, coeffs[1]]
    check(c, 'recovery_coefficients', recovery, [-70, 24, -2])
    check(c, 'factorization_coefficients', recovery,
          [-2*5*7, 2*(5+7), -2])
    check(c, 'known_roots', [poly(recovery, z) for z in [5, 7]], [0, 0])
    check(c, 'block_root', [z for z in [5, 7] if x <= z < x+1], [5])
    check(c, 'proper_factor', 1 < 5 < n and n % 5 == 0, True)


def case7(c):
    n, alpha, m, b, emax = 21, 2, 5, 4, 2
    beta, d = pow(alpha, m, n), 35-5*21
    check(c, 'beta', beta, 11)
    exact_order(c, beta, n, 6, 'global_order')
    exact_order(c, beta, 3, 2, 'order_mod_3')
    check(c, 'component_gcd', gcd(pow(beta, 2, n)-1, n), 3)
    babies = [pow(beta, j, n) for j in range(b)]
    rows = []
    for k in range(2):
        exponent = d + m*emax - m*k*b
        gamma = pow(alpha, exponent, n)
        matches = []
        for j, baby in enumerate(babies):
            if baby == gamma:
                ep = k*b+j-emax
                root = Fraction(m*n, 35-m*ep)
                matches.append(dict(j=j, error=ep,
                                    root=[root.numerator, root.denominator],
                                    integer_root_in_block=(root.denominator == 1 and 3 <= root < 4)))
        rows.append(dict(k=k, exponent=exponent, gamma=gamma, matches=matches))
    c['details'].update(babies=babies, unsafe_giants=rows)
    check(c, 'first_wrong_global_index', rows[0]['matches'][0]['j'], 0)
    check(c, 'true_local_index', (0+emax) % b, 2)
    check(c, 'first_root', rows[0]['matches'][0]['root'], [7, 3])
    check(c, 'second_root', rows[1]['matches'][0]['root'], [7, 1])
    check(c, 'unsafe_root_successes',
          sum(t['integer_root_in_block'] for row in rows for t in row['matches']), 0)


def case8(c):
    exact_order(c, 2, 35, 12, 'alpha_order')
    beta = pow(2, 12, 35)
    check(c, 'beta', beta, 1)
    check(c, 'gcd_is_N', gcd(beta-1, 35), 35)


def case9(c):
    n1, n2 = normalize([0, 2], 6), normalize([0, 3], 6)
    check(c, 'denominators', [n1[1], n2[1]], [3, 2])
    check(c, 'original_image_sizes', [len(image([0, 2], 6)), len(image([0, 3], 6))], [3, 2])
    check(c, 'normalized_image_sizes', [len(image(n1[3], n1[1])), len(image(n2[3], n2[1]))], [3, 2])
    check(c, 'new_bases', [pow(2, n1[1], 35), pow(2, n2[1], 35)], [8, 4])
    check(c, 'old_base', pow(2, 6, 35), 29)


def case10(c):
    check(c, 'sparse_domain_image', image([0, 0, 1], 16, [0, 4, 8, 12]), [0])
    check(c, 'full_domain_image', image([0, 0, 1], 16), [0, 1, 4, 9])
    check(c, 'nonprimitive_image', image([0, 16], 16), [0])
    check(c, 'nonprimitive_normalization', normalize([0, 16], 16)[1], 1)
    check(c, 'Fermat_image', image([0, 0, 0, 0, 1], 5), [0, 1])
    domain = [0, 1]
    pairs = sorted((h % 2, h % 3) for h in domain)
    product = sorted((a, b) for a in image([0, 1], 2, domain)
                     for b in image([0, 1], 3, domain))
    c['details'].update(retained_CRT_pairs=pairs, product_of_projections=product)
    check(c, 'correlated_domain_sizes', [len(pairs), len(product)], [2, 4])


for number, function in enumerate([case1, case2, case3, case4, case5,
                                    case6, case7, case8, case9, case10], 1):
    case = dict(case=number, checks=[], details={})
    try:
        function(case)
    except Exception:
        case['exception'] = traceback.format_exc()
    case['passed'] = ('exception' not in case
                      and all(item['passed'] for item in case['checks']))
    RESULTS.append(case)

count = sum(len(c['checks']) for c in RESULTS)
result = dict(cases=RESULTS, case_count=len(RESULTS), check_count=count,
              passed_cases=sum(c['passed'] for c in RESULTS),
              failed_checks=sum(not t['passed'] for c in RESULTS for t in c['checks']),
              budget_met=count <= 10000)
print(json.dumps(result, indent=2, sort_keys=True))
sys.exit(0 if result['passed_cases'] == 10 and result['budget_met'] else 1)
