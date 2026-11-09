#!/usr/bin/env python3
"""Independent arithmetic reference for H019, with no candidate imports.

Taylor coefficients use the direct binomial formula, never Horner shifting.
Every positive witness is rechecked from N and its exact certificate data.
"""
from fractions import Fraction
import hashlib
import itertools
import math


def prime_certificate():
    """One trial-division verification in the outer runner, charged to setup."""
    p = 65537
    trials = [[a, p % a] for a in range(2, math.isqrt(p)+1)]
    assert all(remainder != 0 for _, remainder in trials)
    return {"prime": p, "method": "all integer divisors 2 through floor(sqrt(p))",
            "trials": trials, "prime_verified": True}


def summary(number):
    width = number.bit_length()
    raw = number.to_bytes((width+7)//8, byteorder="big", signed=False)
    return {"bits": width, "sha256": hashlib.sha256(raw).hexdigest()}


def squarefree(f, witness, progress):
    p = 65537
    derivative = [(j+1)*f[j+1] % p for j in range(len(f)-1)]
    if witness["unit"]:
        s, t = witness["s"], witness["t"]
        assert all(type(v) is int and 0 <= v < p for v in s+t)
        result = [0]*max(1, len(s)+len(f)-1, len(t)+len(derivative)-1)
        for a, b in ((s, f), (t, derivative)):
            for i in range(len(a)):
                for j in range(len(b)):
                    result[i+j] += a[i]*b[j]
                    progress.add("reference_bezout_multiplications")
        assert result[0] % p == 1
        assert all(v % p == 0 for v in result[1:])
        return True
    # A failed sufficient certificate is checked by a separate plain gcd.
    a, b = [v % p for v in f], derivative
    while a and a[-1] == 0:
        a.pop()
    while b and b[-1] == 0:
        b.pop()
    while b:
        rem = a[:]
        while rem and len(rem) >= len(b):
            offset = len(rem)-len(b)
            multiple = rem[-1]*pow(b[-1], p-2, p) % p
            for j in range(len(b)):
                rem[offset+j] = (rem[offset+j]-multiple*b[j]) % p
            while rem and rem[-1] == 0:
                rem.pop()
            progress.add("reference_gcd_steps")
        a, b = b, rem
    assert len(a) != 1
    assert witness["gcd_degree"] == len(a)-1
    return False


def direct_taylor(f, x, y, progress):
    """A_j = sum_i>=j f_i binom(i,j) (x+iy)^(i-j) Q^(d-i+j)."""
    d = len(f)-1
    powers = [(1, 0)]
    for _ in range(d):
        a, b = powers[-1]
        powers.append((a*x-b*y, a*y+b*x))
        progress.add("reference_gaussian_powers")
    coeff = []
    for j in range(d+1):
        real = imag = 0
        for i in range(j, d+1):
            scalar = f[i]*math.comb(i, j)
            real += (scalar*powers[i-j][0]) << (40*(d-i+j))
            imag += (scalar*powers[i-j][1]) << (40*(d-i+j))
            progress.add("reference_binomial_terms")
        coeff.append((real, imag))
    return coeff


def disks(f, centers, expected, radius_bound, claimed, progress):
    q, tq = 2**40, 2**16
    gate = "accepted"
    if len(centers) != expected:
        gate = "disk_count"
    elif any(len(v) != 2 or any(type(c) is not int for c in v) for v in centers):
        gate = "disk_domain"
    elif radius_bound is not None and (radius_bound*q <= tq or any(
            a*a+b*b >= (radius_bound*q-tq)**2 for a, b in centers)):
        gate = "containment"
    else:
        for i in range(len(centers)):
            for j in range(i):
                dist = sum((centers[i][axis]-centers[j][axis])**2 for axis in (0, 1))
                if dist <= 4*tq*tq:
                    gate = "disjointness"
    checks = []
    if gate == "accepted":
        d = len(f)-1
        for index, center in enumerate(centers):
            progress.event("reference_disk", disk_index=index)
            coefficients = direct_taylor(f, center[0], center[1], progress)
            lower = max(map(abs, coefficients[1]))*pow(2, 24*(d-1))
            upper = 0
            for j in range(d+1):
                if j != 1:
                    upper += (abs(coefficients[j][0])+abs(coefficients[j][1]))*pow(2, 24*(d-j))
            hasher = hashlib.sha256()
            for real, imag in coefficients:
                hasher.update((hex(real)+","+hex(imag)+"\n").encode("ascii"))
            checks.append({"index": index, "taylor_sha256": hasher.hexdigest(),
                           "lhs_hex": hex(lower), "rhs_hex": hex(upper),
                           "lhs": summary(lower), "rhs": summary(upper), "strict": lower > upper})
            progress.add("reference_disk_predicates")
            if lower <= upper:
                gate = "disk_rouche"
                break
    actual = {"accepted": gate == "accepted", "gate": gate, "checks": checks}
    assert actual == claimed, "candidate/reference disk witness mismatch"
    return actual["accepted"], gate


def control(case, witness, progress):
    if not squarefree(case["f"], witness["squarefree"], progress):
        return False, "squarefree"
    return disks(case["f"], case["disks"], len(case["f"])-1, None,
                 witness["disk_verification"], progress)


def geometry(centers, claimed, progress):
    q, t = 2**40, Fraction(1, 2**24)
    z = [(Fraction(a, q), Fraction(b, q)) for a, b in centers]
    upper = [max(Fraction(1), abs(a)+abs(b)+t) for a, b in z]
    lower, pairs = {}, []
    for i, j in itertools.combinations(range(len(z)), 2):
        lower[i, j] = max(Fraction(0), max(abs(z[i][0]-z[j][0]), abs(z[i][1]-z[j][1]))-2*t)
        pair = lower[i, j]/(upper[i]*upper[j])
        pairs.append({"i": i, "j": j, "L_times_Q": int(lower[i, j]*q),
                      "delta_lower_num_hex": hex(pair.numerator),
                      "delta_lower_den_hex": hex(pair.denominator)})
        progress.add("reference_geometry_pairs")
    best, argmin = None, None
    for i, j, l in itertools.combinations(range(len(z)), 3):
        value = lower[i, j]*lower[i, l]*lower[j, l]/(6*upper[i]**2*upper[j]**2*upper[l]**2)
        if best is None or value < best:
            best, argmin = value, [i, j, l]
        progress.add("reference_geometry_triples")
    actual = {"U_times_Q": [int(u*q) for u in upper], "pairs": pairs,
              "minimizing_triple": argmin, "kappa_num_hex": hex(best.numerator),
              "kappa_den_hex": hex(best.denominator), "positive": best > 0}
    assert actual == claimed, "candidate/reference rational geometry mismatch"
    return best


def comparison(N, d, H, hstar, kappa, claimed, progress):
    exponent = 5*d*(d-4)
    x, y = kappa.numerator, kappa.denominator
    # Separate factors, independent of the candidate's grouped powering.
    left = x**exponent * hstar**exponent * N**9
    progress.add("reference_comparison_powers", 3)
    right = y**exponent * 20736**(5*d) * 2**(10*d) * 12**(5*d*d) * (d+1)**(5*d)
    right <<= (H.bit_length()-1)*(d+6)*5*d
    progress.add("reference_comparison_powers", 5)
    actual = {"exponent": exponent, "lhs": summary(left), "rhs": summary(right),
              "lhs_factors": [[hex(x), exponent], [hex(hstar), exponent], [hex(N), 9]],
              "rhs_factors": [[hex(y), exponent], [hex(20736), 5*d], [hex(2), 10*d],
                              [hex(12), 5*d*d], [hex(d+1), 5*d], [hex(H), (d+6)*5*d]],
              "ge": left >= right,
              "primitive_upper_count_hex": hex((hstar-1)*(2*hstar-1)*(2*hstar-1)+d-2)}
    assert actual == claimed, "candidate/reference equation (11) mismatch"
    return actual["ge"]


def research(N, witness, progress):
    progress.event("reference_base")
    n = N.bit_length()
    d = {4096: 15, 16384: 22, 65536: 34, 262144: 52}[n]
    assert N > 1 and N % 2 == 1
    assert witness["n"] == n and witness["d"] == d
    f = [int(v, 16) for v in witness["f_hex"]]
    m = int(witness["m_hex"], 16)
    H, hstar = int(witness["H_hex"], 16), int(witness["hstar_hex"], 16)
    hbits = -(-(67473*n)//(20000*d*d))
    assert witness["hbits"] == hbits and H == 2**hbits
    assert hstar >= 1 and (hstar-1)**5 < H**4 <= hstar**5
    value = sum(c*m**j for j, c in enumerate(f))
    progress.add("reference_base_powers", len(f)+2)
    base_ok = (m >= 2 and m**d <= N < (m+1)**d and len(f) == d+1 and
               f[-1] == 1 and all(0 <= c < m for c in f) and value == N)
    assert base_ok == witness["base_ok"]
    if not base_ok:
        return "unknown", "base_domain"
    progress.event("reference_squarefree")
    if not squarefree(f, witness["squarefree"], progress):
        return "unknown", "squarefree_sufficient_failed"
    progress.event("reference_dominance")
    R = 2*H+2
    lhs = f[d-2]*R**(d-2)
    rhs = sum(f[j]*R**j for j in range(d+1) if j != d-2)
    actual = {"R_hex": hex(R), "index": d-2, "strict": lhs > rhs,
              "lhs": summary(lhs), "rhs": summary(rhs)}
    assert actual == witness["dominance"]
    if lhs <= rhs:
        return "unknown", "dominance_sufficient_failed"
    if not witness["approximation"]["converged"]:
        # This is explicitly not a verified certificate of root absence.
        return "unknown", "approximation"
    progress.event("reference_disks")
    accepted, gate = disks(f, witness["disks"], d-2, R,
                           witness["disk_verification"], progress)
    if not accepted:
        return "unknown", gate
    # These d-2 disjoint one-root disks lie within the circle; dominance
    # proves exactly d-2 roots inside it and exactly two exterior roots.
    progress.event("reference_geometry")
    kappa = geometry(witness["disks"], witness["geometry"], progress)
    if kappa <= 0:
        return "unknown", "nonpositive_kappa"
    progress.event("reference_count_comparison")
    if not comparison(N, d, H, hstar, kappa, witness["comparison"], progress):
        return "unknown", "count_inequality"
    progress.event("reference_verified")
    return "pass", "certified_count"
