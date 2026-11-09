#!/usr/bin/env python3
"""One frozen, tiny transition diagnostic; not a full factoring solver."""
import hashlib
import json
import math
from pathlib import Path
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
MODULI = (91, 143, 187)
MARKS = (7, 11, 13, 17)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def d_exact(j):
    return sum(math.comb(j, k) ** 2 * 2 ** k for k in range(j + 1))


class Meter:
    def __init__(self):
        self.max_integer_bits = 0
        self.matrix_products = 0
        self.scalar_products = 0
        self.gcds = 0
        self.inversions = 0
        self.polynomial_multiply_adds = 0

    def see(self, *values):
        for value in values:
            self.max_integer_bits = max(self.max_integer_bits, abs(value).bit_length())


def mm(A, B, modulus, meter):
    meter.matrix_products += 1
    out = [[0, 0], [0, 0]]
    for i in range(2):
        for j in range(2):
            for k in range(2):
                product = A[i][k] * B[k][j]
                raw = out[i][j] + product
                meter.see(product, raw)
                out[i][j] = raw if modulus is None else raw % modulus
    return out


def mv(A, v, modulus, meter):
    out = []
    for row in A:
        terms = [row[i] * v[i] for i in range(2)]
        raw = sum(terms)
        meter.see(*terms, raw)
        out.append(raw if modulus is None else raw % modulus)
    return out


def block_product(a, length, modulus, meter):
    if length == 1:
        A = [[6 * a + 3, -a], [a + 1, 0]]
        D = a + 1
        meter.see(a, D, *(x for row in A for x in row))
        if modulus is not None:
            A = [[x % modulus for x in row] for row in A]
            D %= modulus
        return A, D
    left_len = length // 2
    A, D = block_product(a, left_len, modulus, meter)
    B, E = block_product(a + left_len, length - left_len, modulus, meter)
    raw = E * D
    meter.scalar_products += 1
    meter.see(raw)
    return mm(B, A, modulus, meter), raw if modulus is None else raw % modulus


def scalar_tree(a, length, N, meter):
    if length == 1:
        return ((a + 1) % N, a + 1, a + 1, None, None)
    left_len = length // 2
    left = scalar_tree(a, left_len, N, meter)
    right = scalar_tree(a + left_len, length - left_len, N, meter)
    raw = left[0] * right[0]
    meter.see(raw)
    meter.scalar_products += 1
    return (raw % N, left[1], right[2], left, right)


def measured_gcd(value, N, meter):
    meter.see(value, N)
    meter.gcds += 1
    return math.gcd(value, N)


def descend_full_gcd(tree, N, meter, trace):
    # The caller establishes gcd(tree.product,N)=N.
    while True:
        if tree[3] is None:
            raise AssertionError("gcd=N reached a leaf below N")
        left, right = tree[3], tree[4]
        g = measured_gcd(left[0], N, meter)
        trace.append({"interval": [left[1], left[2]], "product_mod_N": left[0], "gcd": g})
        if 1 < g < N:
            return g
        tree = left if g == N else right


def factor_or_action(N, a, length, residue_pair):
    assert 0 <= a < a + length < N
    meter = Meter()
    A, D = block_product(a, length, N, meter)
    g = measured_gcd(D, N, meter)
    out = {"denominator_mod_N": D, "denominator_gcd": g, "trace": []}
    if g == 1:
        inverse = pow(D, -1, N)
        meter.inversions += 1
        numer = mv(A, residue_pair, N, meter)
        action = []
        for value in numer:
            raw = inverse * value
            meter.see(raw)
            meter.scalar_products += 1
            action.append(raw % N)
        out.update(kind="action", action=action)
    else:
        factor = g
        if g == N:
            tree = scalar_tree(a, length, N, meter)
            factor = descend_full_gcd(tree, N, meter, out["trace"])
        out.update(kind="factor", factor=factor)
    out["meter"] = vars(meter)
    return out


def check_block(N, a, length):
    b = a + length
    initial = [d_exact(a), d_exact(a - 1)]
    endpoint = [d_exact(b), d_exact(b - 1)]
    initial_res = [x % N for x in initial]
    expected = [x % N for x in endpoint]
    outcome = factor_or_action(N, a, length, initial_res)
    if outcome["kind"] == "action":
        assert outcome["action"] == expected, (outcome, expected)
    else:
        g = outcome["factor"]
        assert 1 < g < N and N % g == 0, outcome
    exact_meter = Meter()
    A, D = block_product(a, length, None, exact_meter)
    numerator = mv(A, initial, None, exact_meter)
    assert all(x % D == 0 for x in numerator)
    exact_action = [x // D for x in numerator]
    assert exact_action == endpoint, (exact_action, endpoint)
    lift_meter = Meter()
    lift_modulus = N * D
    lift_meter.see(lift_modulus)
    lifted_A, _ = block_product(a, length, lift_modulus, lift_meter)
    lifted_num = mv(lifted_A, [x % lift_modulus for x in initial], lift_modulus, lift_meter)
    assert all(x % D == 0 for x in lifted_num)
    lifted_action = [x // D % N for x in lifted_num]
    assert lifted_action == expected, (lifted_action, expected)
    return {"N": N, "a": a, "length": length, "denominator_interval": [a + 1, b],
            "input_residues": initial_res, "expected_endpoint": expected,
            "outcome": outcome, "exact_D": D, "exact_D_bits": D.bit_length(),
            "lift_modulus_bits": lift_modulus.bit_length(), "lifted_action": lifted_action,
            "exact_reference_meter": vars(exact_meter), "lifted_meter": vars(lift_meter),
            "status": "pass"}


def check_ambiguity(N, r):
    u, v = d_exact(r - 1), d_exact(r - 2)
    num0 = (6 * r - 3) * u - (r - 1) * v
    num1 = (6 * r - 3) * u - (r - 1) * (v + N)
    assert num0 % r == num1 % r == 0
    first, second = num0 // r, num1 // r
    assert first == d_exact(r)
    assert second - first == -(r - 1) * (N // r)
    assert first % N != second % N
    return {"N": N, "r": r, "input_lifts": [[u, v], [u, v + N]],
            "shared_input_residues": [u % N, v % N],
            "integral_outputs": [first, second], "output_residues": [first % N, second % N],
            "difference": second - first, "status": "expected_obstruction_confirmed"}


def pmul(A, B, precision, N, meter):
    C = [0] * precision
    for i, ai in enumerate(A):
        for j, bj in enumerate(B):
            if i + j >= precision:
                break
            raw = C[i + j] + ai * bj
            meter.see(raw)
            meter.polynomial_multiply_adds += 1
            C[i + j] = raw % N
    return C


def series_newton(N, precision):
    meter = Meter()
    assert math.gcd(2, N) == 1
    inverse2 = (N + 1) // 2
    h = [1]
    stages = [1]
    Q = [1, (-6) % N, 1]
    while len(h) < precision:
        new_precision = min(2 * len(h), precision)
        hh = pmul(h, h, new_precision, N, meter)
        Qhh = pmul(Q, hh, new_precision, N, meter)
        correction = [(-x) % N for x in Qhh]
        correction[0] = (3 - Qhh[0]) % N
        raw_h = pmul(h, correction, new_precision, N, meter)
        h = []
        for value in raw_h:
            raw = value * inverse2
            meter.see(raw)
            meter.scalar_products += 1
            h.append(raw % N)
        stages.append(len(h))
    return h, {"precision_stages": stages, "coefficient_slots_final": len(h), "meter": vars(meter)}


def main():
    started = time.monotonic()
    frozen = HERE / "H007-coefficient-preregistered.md"
    original = HERE.parent / "hypotheses" / "W001-algebra.md"
    source = Path(__file__).resolve()
    cases = []
    for N in MODULI:
        for r in MARKS:
            cases.append((f"block-{N}-r{r}", "block", (N, r - 2, 3)))
        cases.append((f"block-{N}-span", "block", (N, 5, 13)))
    for N in MODULI:
        for r in MARKS:
            if N % r == 0:
                cases.append((f"ambiguity-{N}-r{r}", "ambiguity", (N, r)))
    for N in MODULI:
        for r in MARKS:
            cases.append((f"newton-{N}-r{r}", "newton", (N, r)))
    results_path = HERE / "H007-coefficient-results.jsonl"
    completed = []
    active = None
    status = "pass"
    cache = {}
    with results_path.open("x", encoding="utf-8") as out:
        def emit(record):
            out.write(json.dumps(record, sort_keys=True) + "\n")
            out.flush()
        emit({"type": "begin", "time_unix": time.time(), "python": sys.version,
              "cap_seconds": 60, "source_sha256": sha(source),
              "preregistered_sha256": sha(frozen), "original_report_sha256": sha(original),
              "planned_cases": [x[0] for x in cases]})
        try:
            for case_id, kind, args in cases:
                active = case_id
                if kind == "block":
                    result = check_block(*args)
                elif kind == "ambiguity":
                    result = check_ambiguity(*args)
                else:
                    N, r = args
                    if N not in cache:
                        cache[N] = series_newton(N, 19)
                        emit({"type": "newton_setup", "N": N, **cache[N][1]})
                    actual = cache[N][0][r]
                    expected = d_exact(r) % N
                    assert actual == expected, (N, r, actual, expected)
                    result = {"N": N, "r": r, "actual": actual, "expected": expected, "status": "pass"}
                emit({"type": "case", "case_id": case_id, "kind": kind, **result})
                completed.append(case_id)
                active = None
        except Exception as exc:
            status = "failure"
            emit({"type": "unexpected_failure", "case_id": active, "error": repr(exc),
                  "traceback": traceback.format_exc()})
        remaining = [c[0] for c in cases if c[0] not in completed and c[0] != active]
        summary = {"type": "end", "status": status, "completed": len(completed),
                   "failed_case": active, "unstarted_case_ids": remaining,
                   "elapsed_seconds": time.monotonic() - started}
        emit(summary)
        print(json.dumps(summary, sort_keys=True))
    return 0 if status == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
