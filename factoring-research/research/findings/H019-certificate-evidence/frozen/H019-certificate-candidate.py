#!/usr/bin/env python3
"""Frozen H019 candidate. No imports of project solvers; stdlib only.

Proof links: H017-resultant-tail-supply.md equations (10), (11), (18), (19).
Execution is exclusively through H019-certificate-runner.py's single trial.
All coefficients are ascending. Gaussian integers are (real, imaginary).
"""
import cmath
import hashlib
import importlib.util
import itertools
import json
import math
import os
from pathlib import Path
import sys
import time
import traceback

Q = 1 << 40
S = 1 << 24
TQ = Q // S
P = 65537
DEGREES = {4096: 15, 16384: 22, 65536: 34, 262144: 52}


def write_new(path, data):
    with open(path, "x", encoding="utf-8") as out:
        json.dump(data, out, sort_keys=True, indent=2, allow_nan=False)
        out.write("\n")
        out.flush()
        os.fsync(out.fileno())


class Progress:
    def __init__(self, path):
        self.path = path
        self.started = time.monotonic()
        self.previous = self.started
        self.counters = {}
        self.times = {}
        self.stage = "worker_start"

    def add(self, key, value=1):
        self.counters[key] = self.counters.get(key, 0) + value

    def event(self, stage, **details):
        now = time.monotonic()
        self.times[self.stage] = self.times.get(self.stage, 0.0) + now-self.previous
        self.previous = now
        self.stage = stage
        row = dict(stage=stage, elapsed_seconds=now-self.started,
                   counters=dict(self.counters), stage_seconds=dict(self.times),
                   details=details)
        with open(self.path, "a", encoding="utf-8") as out:
            out.write(json.dumps(row, sort_keys=True, allow_nan=False)+"\n")
            out.flush()
            os.fsync(out.fileno())


def measure_int(v):
    assert v >= 0
    return {"bits": v.bit_length(), "sha256": hashlib.sha256(
        v.to_bytes((v.bit_length()+7)//8, "big")).hexdigest()}


def nth_root_floor(n, d, progress):
    """Integer Newton from an upper bound, with exact terminal correction."""
    if n < 2:
        return n
    x = 1 << ((n.bit_length()+d-1)//d)
    while True:
        y = ((d-1)*x + n//pow(x, d-1))//d
        progress.add("integer_newton_iterations")
        if y >= x:
            break
        x = y
    while pow(x, d) > n:
        x -= 1
        progress.add("integer_root_corrections")
    while pow(x+1, d) <= n:
        x += 1
        progress.add("integer_root_corrections")
    return x


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def poly_sub(a, b):
    return trim([((a[i] if i < len(a) else 0) -
                  (b[i] if i < len(b) else 0)) % P
                 for i in range(max(len(a), len(b)))])


def poly_mul(a, b):
    if not a or not b:
        return []
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] = (c[i+j]+x*y) % P
    return trim(c)


def poly_div(a, b, progress):
    a = trim(a)
    q = [0]*max(0, len(a)-len(b)+1)
    inv = pow(b[-1], -1, P)
    while a and len(a) >= len(b):
        j = len(a)-len(b)
        c = a[-1]*inv % P
        q[j] = c
        for i, v in enumerate(b):
            a[i+j] = (a[i+j]-c*v) % P
        a = trim(a)
        progress.add("modular_division_steps")
    return trim(q), a


def squarefree_certificate(f, progress):
    a = trim([v % P for v in f])
    b = trim([i*f[i] % P for i in range(1, len(f))])
    s0, s1, t0, t1 = [1], [], [], [1]
    while b:
        q, r = poly_div(a, b, progress)
        a, b = b, r
        s0, s1 = s1, poly_sub(s0, poly_mul(q, s1))
        t0, t1 = t1, poly_sub(t0, poly_mul(q, t1))
    if len(a) != 1:
        return {"unit": False, "gcd_degree": len(a)-1}
    v = pow(a[0], -1, P)
    return {"unit": True, "s": [v*x % P for x in s0],
            "t": [v*x % P for x in t0]}


def gm(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def taylor_horner(f, x, y, progress):
    """Q**d times every coefficient of f((x+iy)/Q + Y)."""
    coeff = [(f[-1], 0)]
    qlevel = 1
    for fi in reversed(f[:-1]):
        qlevel *= Q
        shifted = []
        for j in range(len(coeff)+1):
            re, im = gm(coeff[j], (x, y)) if j < len(coeff) else (0, 0)
            if j:
                re += Q*coeff[j-1][0]
                im += Q*coeff[j-1][1]
            if j == 0:
                re += fi*qlevel
            shifted.append((re, im))
        progress.add("candidate_taylor_extensions")
        progress.add("candidate_gaussian_small_multiplications", len(coeff))
        coeff = shifted
    return coeff


def taylor_digest(coeff):
    data = "".join(hex(a)+","+hex(b)+"\n" for a, b in coeff)
    return hashlib.sha256(data.encode("ascii")).hexdigest()


def disk_geometry(disks, expected, R):
    if len(disks) != expected:
        return False, "disk_count"
    if any(len(z) != 2 or any(type(v) is not int for v in z) for z in disks):
        return False, "disk_domain"
    if R is not None:
        if R*Q <= TQ or any(x*x+y*y >= (R*Q-TQ)**2 for x, y in disks):
            return False, "containment"
    for i, j in itertools.combinations(range(len(disks)), 2):
        dx = disks[i][0]-disks[j][0]
        dy = disks[i][1]-disks[j][1]
        if dx*dx+dy*dy <= (2*TQ)**2:
            return False, "disjointness"
    return True, "geometry"


def verify_disks(f, disks, expected, R, progress):
    okay, reason = disk_geometry(disks, expected, R)
    if not okay:
        return {"accepted": False, "gate": reason, "checks": []}
    d = len(f)-1
    checks = []
    for i, (x, y) in enumerate(disks):
        progress.event("candidate_disk", disk_index=i)
        coeff = taylor_horner(f, x, y, progress)
        lhs = max(abs(coeff[1][0]), abs(coeff[1][1])) << (24*(d-1))
        rhs = sum((abs(re)+abs(im)) << (24*(d-j))
                  for j, (re, im) in enumerate(coeff) if j != 1)
        row = {"index": i, "taylor_sha256": taylor_digest(coeff),
               "lhs_hex": hex(lhs), "rhs_hex": hex(rhs),
               "lhs": measure_int(lhs), "rhs": measure_int(rhs),
               "strict": lhs > rhs}
        checks.append(row)
        progress.add("candidate_disk_predicates")
        if lhs <= rhs:
            return {"accepted": False, "gate": "disk_rouche", "checks": checks}
    return {"accepted": True, "gate": "accepted", "checks": checks}


def aberth(f, progress):
    maximum = max(abs(v) for v in f)
    if maximum == 0 or f[-1] == 0:
        return {"converged": False, "reason": "truncation_domain"}, None
    # int/int division scales before conversion, avoiding float(huge integer).
    a = [v/maximum for v in f]
    if a[-1] == 0 or any(not math.isfinite(v) for v in a):
        return {"converged": False, "reason": "normalization_domain"}, None
    k = len(a)-1
    radius = 1 + max(abs(v/a[-1]) for v in a[:-1])
    if not math.isfinite(radius):
        return {"converged": False, "reason": "nonfinite_circle"}, None
    z = [radius*cmath.exp(2j*math.pi*(j+0.5)/k) for j in range(k)]
    for sweep in range(1, 501):
        corrections = []
        for i, zi in enumerate(z):
            value, deriv = complex(a[-1]), 0j
            for aj in reversed(a[:-1]):
                deriv = deriv*zi+value
                value = value*zi+aj
            if deriv == 0:
                return {"converged": False, "reason": "zero_derivative", "sweeps": sweep}, None
            newton = value/deriv
            invsum = 0j
            for j, zj in enumerate(z):
                if j != i:
                    if zi == zj:
                        return {"converged": False, "reason": "collision", "sweeps": sweep}, None
                    invsum += 1/(zi-zj)
                    progress.add("aberth_pair_reciprocals")
            denom = 1-newton*invsum
            if denom == 0:
                return {"converged": False, "reason": "zero_aberth_denominator", "sweeps": sweep}, None
            correction = newton/denom
            if not all(math.isfinite(v) for v in (correction.real, correction.imag)):
                return {"converged": False, "reason": "nonfinite_correction", "sweeps": sweep}, None
            corrections.append(correction)
            progress.add("aberth_updates")
        z = [zi-ci for zi, ci in zip(z, corrections)]
        progress.add("aberth_sweeps")
        if any(not math.isfinite(v) for zi in z for v in (zi.real, zi.imag)):
            return {"converged": False, "reason": "nonfinite_center", "sweeps": sweep}, None
        largest = max(abs(ci) for ci in corrections)
        if largest <= 2**-42:
            disks = [[round(zi.real*Q), round(zi.imag*Q)] for zi in z]
            return {"converged": True, "sweeps": sweep,
                    "cauchy_radius_float_hex": radius.hex(),
                    "max_correction_float_hex": largest.hex(),
                    "centers_float_hex": [[zi.real.hex(), zi.imag.hex()] for zi in z]}, disks
    return {"converged": False, "reason": "500_sweeps", "sweeps": 500}, None


def rational_geometry(disks, progress):
    U = [max(Q, abs(x)+abs(y)+TQ) for x, y in disks]
    L = {}
    pairs = []
    for i, j in itertools.combinations(range(len(disks)), 2):
        l = max(0, max(abs(disks[i][0]-disks[j][0]),
                       abs(disks[i][1]-disks[j][1]))-2*TQ)
        L[i, j] = l
        pn, pd = l*Q, U[i]*U[j]
        g = math.gcd(pn, pd)
        pairs.append({"i": i, "j": j, "L_times_Q": l,
                      "delta_lower_num_hex": hex(pn//g),
                      "delta_lower_den_hex": hex(pd//g)})
        progress.add("candidate_geometry_pairs")
    best = None
    triple = None
    for i, j, l in itertools.combinations(range(len(disks)), 3):
        a = Q**3*L[i, j]*L[i, l]*L[j, l]
        b = 6*U[i]**2*U[j]**2*U[l]**2
        if best is None or a*best[1] < best[0]*b:
            best, triple = (a, b), [i, j, l]
        progress.add("candidate_geometry_triples")
    g = math.gcd(*best)
    a, b = best[0]//g, best[1]//g
    return {"U_times_Q": U, "pairs": pairs, "minimizing_triple": triple,
            "kappa_num_hex": hex(a), "kappa_den_hex": hex(b), "positive": a > 0}


def count_comparison(N, d, H, hstar, geometry, progress):
    x, y = int(geometry["kappa_num_hex"], 16), int(geometry["kappa_den_hex"], 16)
    k, r = d-2, 2
    e = 5*d*(k-2)
    constant = 20736*(2**r)*(12**d)*(d+1)
    lhs = pow(x*hstar, e)*pow(N, 9)
    progress.add("candidate_comparison_powers", 2)
    rhs = (pow(y, e)*pow(constant, 5*d)) << ((H.bit_length()-1)*(d+6)*5*d)
    progress.add("candidate_comparison_powers", 2)
    return {"exponent": e, "lhs": measure_int(lhs), "rhs": measure_int(rhs),
            "lhs_factors": [[hex(x), e], [hex(hstar), e], [hex(N), 9]],
            "rhs_factors": [[hex(y), e], [hex(20736), 5*d], [hex(2), r*5*d],
                            [hex(12), d*5*d], [hex(d+1), 5*d], [hex(H), (d+6)*5*d]],
            "ge": lhs >= rhs,
            "primitive_upper_count_hex": hex((hstar-1)*(2*hstar-1)**2+k)}


def research(N, progress):
    progress.event("candidate_base")
    n = N.bit_length()
    d = DEGREES[n]
    m = nth_root_floor(N, d, progress)
    f, remainder = [], N
    while remainder:
        remainder, digit = divmod(remainder, m)
        f.append(digit)
        progress.add("base_digits")
    hbits = (67473*n+20000*d*d-1)//(20000*d*d)
    H = 1 << hbits
    hstar = nth_root_floor(H**4, 5, progress)
    if hstar**5 < H**4:
        hstar += 1
    w = {"n": n, "d": d, "m_hex": hex(m), "f_hex": [hex(c) for c in f],
         "hbits": hbits, "H_hex": hex(H), "hstar_hex": hex(hstar)}
    base_ok = (m >= 2 and m**d <= N < (m+1)**d and len(f) == d+1 and
               f[-1] == 1 and all(0 <= c < m for c in f))
    value = 0
    for c in reversed(f):
        value = value*m+c
    w["base_ok"] = base_ok and value == N
    if not w["base_ok"]:
        return "unknown", "base_domain", w
    progress.event("candidate_squarefree")
    w["squarefree"] = squarefree_certificate(f, progress)
    if not w["squarefree"]["unit"]:
        return "unknown", "squarefree_sufficient_failed", w
    progress.event("candidate_dominance")
    R = 2*H+2
    terms = [c*pow(R, j) for j, c in enumerate(f)]
    lhs, rhs = terms[d-2], sum(terms)-terms[d-2]
    w["dominance"] = {"R_hex": hex(R), "index": d-2, "strict": lhs > rhs,
                      "lhs": measure_int(lhs), "rhs": measure_int(rhs)}
    if lhs <= rhs:
        return "unknown", "dominance_sufficient_failed", w
    progress.event("candidate_aberth")
    try:
        approx, disks = aberth(f[:d-1], progress)
    except (ArithmeticError, ValueError) as error:
        approx, disks = {"converged": False, "reason": "approximation_error",
                         "exception": type(error).__name__, "message": str(error)}, None
    w["approximation"] = approx
    if disks is None:
        return "unknown", "approximation", w
    w["disks"] = disks
    progress.event("candidate_disks")
    w["disk_verification"] = verify_disks(f, disks, d-2, R, progress)
    if not w["disk_verification"]["accepted"]:
        return "unknown", w["disk_verification"]["gate"], w
    progress.event("candidate_geometry")
    w["geometry"] = rational_geometry(disks, progress)
    if not w["geometry"]["positive"]:
        return "unknown", "nonpositive_kappa", w
    progress.event("candidate_count_comparison")
    w["comparison"] = count_comparison(N, d, H, hstar, w["geometry"], progress)
    if not w["comparison"]["ge"]:
        return "unknown", "count_inequality", w
    return "pass", "certified_count", w


def control(case, progress):
    f, disks = case["f"], case["disks"]
    sf = squarefree_certificate(f, progress)
    w = {"squarefree": sf}
    if not sf["unit"]:
        return False, "squarefree", w
    w["disk_verification"] = verify_disks(f, disks, len(f)-1, None, progress)
    return w["disk_verification"]["accepted"], w["disk_verification"]["gate"], w


def load_reference():
    path = Path(__file__).with_name("H019-certificate-reference.py")
    spec = importlib.util.spec_from_file_location("h019_independent_reference", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def worker(input_path, prefix):
    progress = Progress(prefix+"-events.jsonl")
    progress.event("worker_start")
    try:
        payload = json.loads(Path(input_path).read_text())
        reference = load_reference()
        if "controls" in payload:
            rows = []
            for case in payload["controls"]:
                progress.event("control_candidate", control=case["id"])
                accepted, gate, witness = control(case, progress)
                write_new(prefix+"-"+case["id"]+"-witness.json", witness)
                progress.event("control_reference", control=case["id"])
                ra, rg = reference.control(case, witness, progress)
                okay = (accepted == ra == case["expected_accept"] and
                        gate == rg == case["expected_gate"])
                row = {"id": case["id"], "status": "pass" if okay else "verification_failure",
                       "candidate_accepted": accepted, "candidate_gate": gate,
                       "reference_accepted": ra, "reference_gate": rg}
                rows.append(row)
                write_new(prefix+"-"+case["id"]+"-result.json", row)
                progress.event("control_complete", **row)
            result = {"status": "pass" if all(r["status"] == "pass" for r in rows)
                      else "verification_failure", "controls": rows}
        else:
            N = int(payload["N_hex"], 16)
            status, reason, witness = research(N, progress)
            write_new(prefix+"-witness.json", witness)
            progress.event("candidate_complete", status=status, reason=reason)
            verified_status, verified_reason = reference.research(N, witness, progress)
            consistent = (status, reason) == (verified_status, verified_reason)
            result = {"status": status if consistent else "verification_failure",
                      "reason": reason, "reference_status": verified_status,
                      "reference_reason": verified_reason, "independent_match": consistent}
            if status == "pass" and consistent:
                result["primitive_upper_count_hex"] = witness["comparison"]["primitive_upper_count_hex"]
                result["kappa_num_hex"] = witness["geometry"]["kappa_num_hex"]
                result["kappa_den_hex"] = witness["geometry"]["kappa_den_hex"]
        progress.event("worker_complete", status=result["status"])
        result.update(counters=progress.counters, stage_seconds=progress.times,
                      elapsed_seconds=time.monotonic()-progress.started)
        write_new(prefix+"-result.json", result)
    except Exception as error:
        result = {"status": "verification_failure" if isinstance(error, AssertionError) else "error",
                  "exception": type(error).__name__, "message": str(error),
                  "traceback": traceback.format_exc()}
        progress.event("worker_exception", **result)
        write_new(prefix+"-result.json", result)


if __name__ == "__main__":
    if len(sys.argv) != 4 or sys.argv[1] != "--worker":
        raise SystemExit("Use the one-shot frozen runner; worker needs N-only input and output prefix.")
    worker(sys.argv[2], sys.argv[3])
