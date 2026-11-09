"""Fixed, preregistered exact W013 review fixtures; not a factoring benchmark."""
from fractions import Fraction as F
from math import comb, gcd, isqrt, prod
import json

CHECKS = 0
RESULTS = []


def check(condition, label):
    global CHECKS
    CHECKS += 1
    assert CHECKS <= 500, "assertion budget exceeded"
    assert condition, label


def bounded(value):
    if isinstance(value, int):
        assert abs(value).bit_length() <= 64, "integer bit budget exceeded"
    elif isinstance(value, F):
        bounded(value.numerator)
        bounded(value.denominator)
    elif isinstance(value, (list, tuple)):
        for item in value:
            bounded(item)
    elif isinstance(value, dict):
        for item in value.values():
            bounded(item)
    return value


def record(name, value):
    bounded(value)
    RESULTS.append({"case": name, "status": "pass", "evidence": value})


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return bounded(a)


def add(a, b):
    return trim([(a[i] if i < len(a) else 0) +
                 (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])


def scale(a, k):
    return trim([k * x for x in a])


def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    assert len(c) <= 5, "degree budget exceeded"
    return trim(c)


def ev(a, x):
    v = 0
    for c in reversed(a):
        v = bounded(v * x + c)
    return v


def shift(a, x):
    return trim([sum(a[j] * comb(j, k) * x ** (j-k)
                     for j in range(k, len(a))) for k in range(len(a))])


def divide_x_plus(a, x):
    a = trim(a)
    if len(a) == 1:
        return [0], a[0]
    c = [0] * (len(a) - 1)
    c[-1] = a[-1]
    for k in range(len(c) - 2, -1, -1):
        c[k] = a[k+1] - x * c[k+1]
    return bounded(c), bounded(a[0] - x * c[0])


def roots_le_two(a):
    """Only fixture degrees <= 2; no factor enumeration or interval scan."""
    a = trim(a)
    check(a != [0], "top-level recovery polynomial is nonzero")
    if len(a) == 1:
        return []
    if len(a) == 2:
        return [-a[0] // a[1]] if -a[0] % a[1] == 0 else []
    assert len(a) == 3
    c, b, q = a
    disc = bounded(b*b - 4*q*c)
    if disc < 0:
        return []
    s = isqrt(disc)
    if s*s != disc:
        return []
    return sorted({v // (2*q) for v in (-b-s, -b+s) if v % (2*q) == 0})


def order_witness(n, alpha, order, prime_divisors):
    check(gcd(n, alpha) == 1, "supplied alpha is a unit")
    check(pow(alpha, order, n) == 1, "supplied order annihilates alpha")
    for ell in prime_divisors:
        check(order % ell == 0 and pow(alpha, order // ell, n) != 1,
              "fixed prime-divisor order witness")
    assert len(prime_divisors) + 1 <= 6


def consumer(n, alpha, baby_size, x, q, a, error, p, order, prime_divisors,
             bypass_component=False):
    # The block has H=1 in every preregistered fixture.
    check(n <= 49 and x == p and n % p == 0, "fixed input and block")
    order_witness(n, alpha, order, prime_divisors)
    check(order >= baby_size, "global order premise")
    true_error = ev(a, 0) - q * (n // p)
    check(abs(F(ev(a, 0)) - F(q*n, x)) <= error, "public bound at only block point")
    public = bounded(ev(a, 1-x) - q*n)
    check((public - true_error) % (p-1) == 0, "equation (1), including p=2")
    beta = [pow(alpha, j, n) for j in range(baby_size)]
    early = [(j, gcd(beta[j]-1, n)) for j in range(1, baby_size)
             if gcd(beta[j]-1, n) != 1]
    for _, g in early:
        check(1 < g < n, "proper component-order gcd")
    if early and not bypass_component:
        return {"early_gcds": early, "factor": early[0][1]}
    count = (2*error + baby_size) // baby_size
    check(count <= 4, "giant budget")
    k0, j0 = divmod(true_error + error, baby_size)
    check(0 <= k0 < count and 0 <= j0 < baby_size, "signed target coverage")
    exponents = [bounded(public+error-k*baby_size) for k in range(count)]
    gamma = [pow(alpha, t, n) for t in exponents]
    check(gamma[k0] % p == beta[j0] % p, "true component collision")
    matches, remaining, found = [], [], []
    for k, value in enumerate(gamma):
        js = [j for j, baby in enumerate(beta) if baby == value]
        check(len(js) <= 1, "at most one global baby match")
        if not js:
            remaining.append(value)
            continue
        j = js[0]
        e = k*baby_size+j-error
        recovery = add(mul([0, 1], add(shift(a, -x), [-e])), [-q*n])
        rr = roots_le_two(recovery)
        in_block = [r for r in rr if x <= r < x+1]
        accepted = [r for r in in_block if 1 < r < n and n % r == 0]
        matches.append({"k": k, "j": j, "error": e, "polynomial": recovery,
                        "integer_roots": rr, "block_roots": in_block,
                        "accepted": accepted})
        found += accepted
        if k == k0 and not bypass_component:
            check(j == j0 and p in accepted, "safe removal of true giant")
    batch = []
    for j, baby in enumerate(beta):
        diffs = [bounded(baby - v) for v in remaining]
        check(all(t % n != 0 for t in diffs), "all global matches removed")
        g = gcd(prod(diffs), n)
        leaf_gcds = [gcd(t, n) for t in diffs]
        batch.append({"j": j, "gcd": g, "leaf_gcds": leaf_gcds})
        if 1 < g < n:
            found.append(g)
        elif g == n:
            leaves = [z for z in leaf_gcds if 1 < z < n]
            check(bool(leaves), "full product gcd has proper leaf")
            found.append(leaves[0])
    if not bypass_component:
        check(bool(found), "covered prime yields a proper factor")
    return {"N": n, "B": baby_size, "true_error": true_error,
            "public_exponent": public, "beta": beta, "giant_exponents": exponents,
            "giants": gamma, "true_pair": [k0, j0], "global_matches": matches,
            "remaining": remaining, "batch": batch, "factors": sorted(set(found)),
            "ignored_component_gcds": early if bypass_component else []}


def batch_full(n, alpha, size, exps, expected, order, primes):
    order_witness(n, alpha, order, primes)
    beta = [pow(alpha, j, n) for j in range(size)]
    vv = [pow(alpha, t, n) for t in exps]
    check(all(gcd(beta[j]-1, n) == 1 for j in range(1, size)), "clean component order")
    check(not set(beta).intersection(vv), "no global matches in retained batch")
    diffs = [1-v for v in vv]
    g = gcd(prod(diffs), n)
    leaves = [gcd(t, n) for t in diffs]
    check(g == n and leaves == expected, "full product with proper leaf gcds")
    return {"N": n, "beta": beta, "giants": vv, "product_gcd": g,
            "leaf_gcds": leaves}


def main():
    record("01_signed_lower", consumer(15, 2, 2, 3, 2, [9], 1, 3, 4, [2]))
    record("02_signed_upper_partial_chunk", consumer(15, 2, 2, 3, 2, [11], 1, 3, 4, [2]))
    record("03_zero_error_composite_q", consumer(35, 2, 3, 5, 3, [21], 0, 5, 12, [2, 3]))
    record("04_B1_p2_nonsemiprime", consumer(12, 5, 1, 2, 1, [6], 0, 2, 2, [2]))
    record("05_prime_power", consumer(27, 2, 2, 3, 1, [9], 0, 3, 18, [2, 3]))
    wrong = consumer(35, 2, 3, 5, 1, [7], 5, 5, 12, [2, 3])
    check(wrong["global_matches"][0]["error"] == -4 and
          wrong["global_matches"][0]["integer_roots"] == [], "paid wrong global match")
    check(wrong["giants"][1] in wrong["remaining"], "true giant survives wrong match")
    record("06_wrong_global_match", wrong)
    correct = consumer(21, 2, 4, 3, 1, [7], 2, 3, 6, [2, 3])
    unsafe = consumer(21, 2, 4, 3, 1, [7], 2, 3, 6, [2, 3], True)
    check(correct["factor"] == 3, "mandatory precheck catches invalid bypass")
    check(unsafe["factors"] == [] and unsafe["remaining"] == [], "unsafe deletion loses coverage")
    record("07_component_order_control", {"correct": correct, "deliberate_bypass": unsafe})
    record("08_squarefree_full_product", batch_full(35, 2, 3, [3, 4], [7, 5], 12, [2, 3]))
    pp = batch_full(49, 3, 2, [6, 12], [7, 7], 42, [2, 3, 7])
    repeated = batch_full(49, 3, 2, [6, 6], [7, 7], 42, [2, 3, 7])
    dedup_gcd = gcd(1-pow(3, 6, 49), 49)
    check(dedup_gcd == 7, "dedup preserves component collision")
    record("09_prime_power_full_product", {"distinct": pp, "repeated": repeated,
                                          "dedup_gcd": dedup_gcd})
    repeated_root = consumer(49, 1, 1, 7, 1, [7, -1], 0, 7, 1, [])
    check(repeated_root["global_matches"][0]["polynomial"] == [-49, 14, -1],
          "repeated root polynomial")
    record("10_repeated_integer_root", repeated_root)

    n, p, cofactor, x, e = 35, 5, 7, 5, 72
    aa, bb = [114, 72, 1], [-4, 3, 2]
    cc, b = divide_x_plus(bb, 0)
    uu = add(aa, scale(cc, -n))
    check(cc == [3, 2] and b == -4 and uu == [9, 2, 1], "normal form")
    check(ev(aa, p)-ev(bb, p)*cofactor == ev(uu, p)-b*cofactor == e,
          "integer residual preservation")
    public = ev(aa, 1)-n*ev(bb, 1)
    check(public == ev(uu, 1)-b*n, "public exponent preservation")
    rr = add(mul([0, 1], add(aa, [-e])), scale(bb, -n))
    normalized = add(mul([0, 1], add(uu, [-e])), [-b*n])
    check(rr == normalized and ev(rr, p) == 0, "recovery polynomial preservation")
    ab, bb_block = shift(aa, x), shift(bb, x)
    cb, block_b = divide_x_plus(bb_block, x)
    ub = add(ab, scale(cb, -n))
    check(block_b == ev(bb_block, -x) == b and ev(bb_block, 0) == 61,
          "block remainder uses -X")
    check(ub == shift(uu, x), "block numerator identity")
    check(ev(ab, 1-x)-n*ev(bb_block, 1-x) == ev(ub, 1-x)-b*n == public,
          "block public exponent")
    rb = add(mul([x, 1], add(ab, [-e])), scale(bb_block, -n))
    check(rb == add(mul([x, 1], add(ub, [-e])), [-b*n]), "block recovery identity")
    check(add(mul([0, 1], add(scale(uu, -1), [e])), [b*n]) == scale(rr, -1),
          "negative b handled by sign reversal")
    record("11_polynomial_block_normalization", {"A_prime": uu, "b": b,
           "B_block": bb_block, "A_prime_block": ub, "error": e,
           "public_exponent": public, "recovery": rr, "block_recovery": rb})

    zero_cases = []
    for aa0, true_e in [([35], 0), ([37], 2), ([35, 1], 5)]:
        cc0, bb0 = divide_x_plus([0, 1], 0)
        uu0 = add(aa0, scale(cc0, -35))
        rr0 = add(mul([0, 1], add(uu0, [-true_e])), [-bb0*35])
        check((rr0 == [0]) == (bb0 == 0 and trim(uu0) == [true_e]),
              "zero polynomial characterization")
        zero_cases.append({"A": aa0, "normalized": uu0, "e": true_e, "recovery": rr0})
    check(zero_cases[0]["recovery"] == zero_cases[1]["recovery"] == [0], "exact/shifted degeneracy")
    check(zero_cases[2]["recovery"] == [0, -5, 1], "b=0 nonconstant remains usable")
    check(ev([-5, 1], 5) == 0 and 1-ev([-5, 1], 5)*7 == 1,
          "zero rational denominator has defined residual only")
    record("12_zero_polynomial_and_denominator", {"cases": zero_cases,
           "zero_denominator_ratio": "undefined", "zero_denominator_residual": 1})

    table = []
    expect = [F(1, 5), F(2, 9), F(1, 4), F(11, 40)]
    for d in (1, 2, 3, 4):
        h = F(2*(2*d+1), (d+1)*(d+4))
        ee = 1-h
        n_cost = (1-h)/2
        check(n_cost == expect[d-1], "formal unsaturated exponent")
        check(ee == h*F(d+2, 2)-F(d, d+1), "formal Taylor balance")
        table.append({"d": d, "H_X_exponent": str(h), "E_X_exponent": str(ee),
                      "E_over_H_X_exponent": str(ee-h), "N_cost_exponent": str(n_cost)})
    h, ee = F(4, 9), F(5, 9)
    qexp = 9*h-3*ee
    check(ee > h and ee < 2*h, "quartic active coordinates exactly 2,3,4")
    check(qexp+5*h-4 == ee and (1-h)/2 == F(5, 18), "saturated quartic budget")
    check(F(11, 40) < F(5, 18), "formal unsaturated quartic understated budget")
    record("13_fixed_degree_budget_arithmetic", {"formal": table,
           "corrected_quartic": {"H_X_exponent": str(h), "E_X_exponent": str(ee),
                                  "q_X_exponent": str(qexp), "N_cost_exponent": "5/18"}})
    check(len(RESULTS) == 13, "exactly preregistered case count")
    print(json.dumps({"status": "pass", "cases": len(RESULTS), "assertions": CHECKS,
                      "benchmark": False, "results": RESULTS}, indent=2))


if __name__ == "__main__":
    main()
