"""Scalar candidate. Inputs are N, a, R and charged public-N setup only.

No factors, corpus labels, diagnostic results, coefficient jets or lookups.
"""


def scalar_binary_power(base, exponent, modulus, m):
    m.mark("power_begin", base, exponent, modulus, detail="public_normalizer")
    base = m.mod(base, modulus)
    acc = base
    bits = bin(exponent)[3:]
    for bit in bits:
        m.mark("power_square_stage", exponent, modulus, detail="scalar")
        acc = m.mmul(acc, acc, modulus)
        if bit == "1":
            m.mark("power_multiply_stage", exponent, modulus, detail="scalar")
            acc = m.mmul(acc, base, modulus)
    return acc


def public_setup(N, R, m):
    m.check("odd_N_and_R", N >= 3 and R >= 1, N, R)
    twice_R = m.mul(2, R)
    out_exp = m.add(twice_R, 1)
    big_exp = m.add(twice_R, 3)
    Nm1 = m.sub(N, 1)
    n, parity_remainder = m.divmod(Nm1, 2)
    m.check("N_is_odd", parity_remainder == 0, parity_remainder)
    m.mark("power_begin", N, big_exp, detail="public_moduli_and_digit_powers")
    # Fixed short chain for all public N powers, not an N-step exponent loop.
    powers = [1, N]
    for exponent in range(2, big_exp + 1):
        m.mark("public_power_stage", exponent, N)
        powers.append(m.mul(powers[-1], N))
    Mbig, Mout = powers[big_exp], powers[out_exp]
    normalizer_power = scalar_binary_power(-4, n, Mout, m)
    digit_powers = []
    for r in range(1, R + 1):
        exponent = m.mul(2, r)
        digit_powers.append(powers[exponent])
    return {"N": N, "R": R, "n": n, "Mbig": Mbig, "Mout": Mout,
            "N2": powers[2], "digit_powers": digit_powers,
            "normalizer_power": normalizer_power, "powers": powers}


def pair_binary_power(z, delta, exponent, modulus, m):
    m.mark("power_begin", z, delta, exponent, modulus, detail="quadratic_pair")
    # Unit input gives 0 < z < N^2 and 0 < delta < N^4 < modulus.
    A, B = z, 1
    for bit in bin(exponent)[3:]:
        m.mark("power_square_stage", exponent, modulus, detail="pair")
        aa = m.mmul(A, A, modulus)
        bb = m.mmul(B, B, modulus)
        dbb = m.mmul(delta, bb, modulus)
        ab = m.mmul(A, B, modulus)
        A, B = m.madd(aa, dbb, modulus), m.madd(ab, ab, modulus)
        if bit == "1":
            m.mark("power_multiply_stage", exponent, modulus, detail="pair_base")
            az = m.mmul(A, z, modulus)
            db = m.mmul(delta, B, modulus)
            bz = m.mmul(B, z, modulus)
            A, B = m.madd(az, db, modulus), m.madd(A, bz, modulus)
    return A, B


def run_case(N, a, R, setup, record, m):
    m.check("candidate_input_contract", N == setup["N"] and R == setup["R"]
            and 0 <= a < N, N, a, R)
    initial = m.gcd(a, N)
    record["initial_gcd"] = initial
    m.mark("branch_classification", a, N, initial, detail="initial_gcd")
    if a == 0:
        record["initial_status"] = "a0_skip"
        return
    if 1 < initial < N:
        record["initial_status"] = "initial_proper_factor"
        return
    m.check("nonzero_remaining_is_unit", initial == 1, initial, N)
    record["initial_status"] = "unit"
    z = m.mul(N, a)
    delta = m.sub(m.mul(z, z), 4)
    record.update({"z": z, "Delta": delta})
    A, B = pair_binary_power(z, delta, N, setup["Mbig"], m)
    record.update({"A": A, "B": B})
    quotient, remainder = m.divmod(A, setup["N2"])
    record["A_div_N2"] = {"quotient": quotient, "remainder": remainder}
    record["identity_outcomes"]["A_divisible_N2"] = remainder == 0
    m.check("A_divisible_N2", remainder == 0, A, setup["N2"], remainder)
    denominator = m.mmul(a, setup["normalizer_power"], setup["Mout"])
    inverse = m.inverse(denominator, setup["Mout"])
    V = m.mmul(quotient, inverse, setup["Mout"])
    record.update({"normalizing_denominator": denominator,
                   "normalizing_inverse": inverse, "V": V})
    for r, power in enumerate(setup["digit_powers"], 1):
        m.mark("digit_stage", r, power, N)
        digit_quotient, _ = m.divmod(V, power)
        digit = m.mod(digit_quotient, N)
        g = m.gcd(digit, N)
        record["digits"].append({"r": r, "d": digit, "gcd": g})
