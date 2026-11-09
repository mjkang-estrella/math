"""Diagnostics only. Known factors never enter candidate functions."""


def setup_reference(N, R, candidate_setup, facts, matrix_enabled, m):
    p, q = facts
    product = m.mul(p, q)
    coprime30 = m.gcd(N, 30)
    twice_R = m.mul(2, R)
    threshold = m.add(twice_R, 1)
    m.check("reference_factor_product_and_size", product == N and p > threshold
            and q > threshold, product, N, p, q, threshold)
    m.check("corpus_coprime_30", coprime30 == 1, coprime30)
    inv24 = m.inverse(24, N)
    inv640 = m.inverse(640, N)
    m.check("inverse_24_identity", m.mmul(24, inv24, N) == 1, 24, inv24, N)
    m.check("inverse_640_identity", m.mmul(640, inv640, N) == 1, 640, inv640, N)
    result = {"known_factors": facts, "inv24": inv24, "inv640": inv640,
              "coprime30": coprime30, "threshold": threshold}
    if matrix_enabled:
        M = candidate_setup["Mbig"]
        result["half_inverse"] = m.inverse(2, M)
        m.check("inverse_2_identity", m.mmul(2, result["half_inverse"], M) == 1,
                2, result["half_inverse"], M)
    return result


def classify(value, g, N, facts, m):
    # Classification is derived from the measured gcd; this is not a second
    # independent gcd algorithm. Direct divisibility is still checked exactly.
    m.mark("branch_classification", value, g, N, detail="gcd_factor_properties")
    cofactor, remainder = m.divmod(N, g)
    _, value_remainder = m.divmod(value, g)
    category = "gcd_1" if g == 1 else "gcd_N" if g == N else "proper"
    valid = (1 <= g <= N and remainder == 0 and value_remainder == 0
             and g in (1, facts[0], facts[1], N))
    m.check("gcd_witness_valid", valid, value, g, N, remainder, value_remainder)
    support = [p for p in facts if g == N or g == p]
    return {"category": category, "cofactor": cofactor, "divides_N": remainder == 0,
            "divides_value": value_remainder == 0, "proper": 1 < g < N,
            "known_prime_support": support, "allowed_known_gcd": valid}


def matrix_multiply(X, Y, modulus, m):
    # Dense, ordinary 2x2 matrix product: 8 scalar products and 4 sums.
    # This routine does not call the pair routine or use Delta.
    result = []
    for i in range(2):
        row = []
        for j in range(2):
            left = m.mmul(X[i][0], Y[0][j], modulus)
            right = m.mmul(X[i][1], Y[1][j], modulus)
            row.append(m.madd(left, right, modulus))
        result.append(row)
    return result


def matrix_binary_power(z, N, modulus, m):
    m.mark("power_begin", z, N, modulus, detail="direct_matrix")
    twice_z = m.mmul(2, z, modulus)
    minus_four = m.mod(-4, modulus)
    base = [[twice_z, minus_four], [1, 0]]
    acc = [base[0][:], base[1][:]]
    for bit in bin(N)[3:]:
        m.mark("power_square_stage", N, modulus, detail="matrix")
        acc = matrix_multiply(acc, acc, modulus, m)
        if bit == "1":
            m.mark("power_multiply_stage", N, modulus, detail="matrix")
            acc = matrix_multiply(acc, base, modulus, m)
    return acc


def check_case(record, setup, ref, do_matrix, m):
    N, a = record["N"], record["a"]
    record["initial_factor_properties"] = classify(a, record["initial_gcd"], N,
                                                     ref["known_factors"], m)
    if record["initial_status"] != "unit":
        return
    V = record["V"]
    residue = m.mod(V, setup["N2"])
    record["identity_outcomes"]["V_mod_N2_is_1"] = residue == 1
    m.check("V_mod_N2_is_1", residue == 1, residue, setup["N2"])
    m.check("V_canonical", 0 <= V < setup["Mout"], V, setup["Mout"])
    a2 = m.mul(a, a)
    expected_d1 = m.mmul(a2, ref["inv24"], N)
    a4 = m.mmul(a2, a2, N)
    leading = m.mmul(m.mmul(3, a4, N), ref["inv640"], N)
    r = m.mod(m.sub(0, a2), 24)
    numerator = m.add(a2, r)
    exact_quotient, rem = m.divmod(numerator, 24)
    record["formula_reference"] = {"a2": a2, "a4_mod_N": a4, "r": r,
                                    "second_quotient": exact_quotient,
                                    "second_quotient_remainder": rem,
                                    "expected_d1": expected_d1}
    record["identity_outcomes"]["second_quotient_exact"] = rem == 0
    m.check("second_quotient_exact", rem == 0, numerator, 24, rem)
    expected_d2 = m.msub(leading, exact_quotient, N)
    record["formula_reference"]["expected_d2"] = expected_d2
    for key, actual, expected in (
        ("d1_formula", record["digits"][0]["d"], expected_d1),
        ("d2_formula", record["digits"][1]["d"], expected_d2),
    ):
        record["identity_outcomes"][key] = actual == expected
        m.check(key, actual == expected, actual, expected)
    for digit in record["digits"]:
        m.check("digit_canonical", 0 <= digit["d"] < N, digit["d"], N)
        digit["factor_properties"] = classify(digit["d"], digit["gcd"], N,
                                               ref["known_factors"], m)
    record["identity_outcomes"]["d1_gcd_is_unit"] = record["digits"][0]["gcd"] == 1
    m.check("d1_gcd_is_unit", record["digits"][0]["gcd"] == 1,
            record["digits"][0]["gcd"], N)
    if do_matrix:
        mat = matrix_binary_power(record["z"], N, setup["Mbig"], m)
        trace = m.madd(mat[0][0], mat[1][1], setup["Mbig"])
        half_trace = m.mmul(trace, ref["half_inverse"], setup["Mbig"])
        ok = half_trace == record["A"]
        record["matrix_reference"] = {"matrix_power": mat, "trace": trace,
                                       "half_trace": half_trace, "matches_A": ok}
        record["identity_outcomes"]["matrix_half_trace_matches_A"] = ok
        m.check("matrix_half_trace_matches_A", ok, half_trace, record["A"])
