#!/usr/bin/env python3
"""Frozen H014 diagnostic; run only after root's independent code review.

This is an exact tiny-domain information screen, NOT an ECDLP solver, a bit-cost
model, or a CPU/GPU throughput benchmark. No numerical self-tests run on import.

Accounting follows H005: field arithmetic and its reduction are separate events;
the underlying integer arithmetic is not counted a second time. Integer/scalar
arithmetic, comparisons, explicit loops, powers/inverses (calls AND their actual
operations), group calls AND field operations, table reads/writes/initialization
entries, PRNG draws/rejections and swaps are charged. A compound equality is one
abstract comparison. Loop events include iterator advancement. Algorithm-table
hashing internals are not expanded into CPU operations. All tables are deliberately
retained until reporting, so the storage-entry ledger includes completed fields.

Excluded: interpreter dispatch, allocator internals, ledger/counter bookkeeping,
ordinary assignments and tuple unpacking/indexing of fixed-size records, exception
formatting, source hashing and JSON serialization. Output-only records are metadata;
the algorithm never reads them to obtain mathematical answers. Control arithmetic,
PRNG work, mathematical loops and accesses to algorithm caches are NOT metadata.
Final source hashing and serialization occur after the measured arithmetic timer.
Imports and immutable source constants precede the ledger; all algorithm-table
allocation, field certification and candidate searches follow its creation.
"""

from collections import Counter
import hashlib
import json
from pathlib import Path
import time


MAX_EVENTS = 1_000_000
MAX_SECONDS = 60.0
FIELDS = (59, 101, 251)
CANDIDATE_LIMIT = 256
ZETA_POWERS = ((1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1))
SEEDS = (7, 19, 43)
MISSING = object()


class BudgetStop(Exception):
    pass


class CorrectnessFailure(Exception):
    pass


class Ledger:
    def __init__(self):
        self.started = time.monotonic()
        self.total = 0
        self.phase = "initialization"
        self.categories = Counter()
        self.phases = {}
        self.storage = {}
        self.tables = []
        self.storage_entries = 0
        self.peak_entries = 0

    def tick(self, category, amount=1):
        if time.monotonic() - self.started >= MAX_SECONDS:
            raise BudgetStop("global wall-time cap exhausted")
        if self.total + amount > MAX_EVENTS:
            raise BudgetStop("global instrumented-event cap exhausted")
        self.total += amount
        self.categories[category] += amount
        self.phases.setdefault(self.phase, Counter())[category] += amount

    def eq(self, a, b):
        self.tick("comparisons")
        return a == b

    def lt(self, a, b):
        self.tick("comparisons")
        return a < b

    def require(self, condition, message):
        self.tick("assertion_checks")
        if not condition:
            raise CorrectnessFailure(message)

    def add(self, a, b):
        self.tick("integer_adds")
        return a + b

    def sub(self, a, b):
        self.tick("integer_subs")
        return a - b

    def mul(self, a, b):
        self.tick("integer_muls")
        return a * b

    def neg(self, a):
        self.tick("integer_negations")
        return -a

    def mod(self, a, b):
        self.tick("integer_remainders")
        return a % b

    def divmod(self, a, b):
        self.tick("integer_divmods")
        return divmod(a, b)

    def shift(self, a, bits=1):
        self.tick("integer_shifts")
        return a >> bits

    def bit(self, a):
        self.tick("integer_bit_operations")
        return a & 1

    def xor(self, a, b):
        self.tick("integer_bit_operations")
        return a ^ b

    def fixed_read(self, values, index):
        self.tick("table_reads")
        return values[index]

    def register(self, table, name):
        # This registry and its updates are storage-instrumentation bookkeeping.
        self.tables.append(table)
        self.storage[name] = 0

    def grew(self, name):
        self.storage[name] += 1
        self.storage_entries += 1
        self.peak_entries = max(self.peak_entries, self.storage_entries)


class Vector:
    def __init__(self, L, name):
        self.L, self.name, self.values = L, name, []
        L.register(self, name)

    def append(self, value):
        self.L.tick("table_initialization_entries")
        self.L.tick("table_writes")
        self.values.append(value)
        self.L.grew(self.name)

    def get(self, index):
        self.L.tick("table_reads")
        return self.values[index]

    def put(self, index, value):
        self.L.tick("table_writes")
        self.values[index] = value

    def length(self):
        self.L.tick("table_reads")
        return len(self.values)


class Table:
    def __init__(self, L, name):
        self.L, self.name, self.values = L, name, {}
        L.register(self, name)

    def get(self, key):
        self.L.tick("table_reads")
        return self.values.get(key, MISSING)

    def put_new(self, key, value):
        self.L.require(self.L.eq(self.get(key), MISSING), "duplicate new table key")
        self.L.tick("table_initialization_entries")
        self.L.tick("table_writes")
        self.values[key] = value
        self.L.grew(self.name)

    def length(self):
        self.L.tick("table_reads")
        return len(self.values)


def prime(n, L):
    L.tick("primality_calls")
    if L.lt(n, 2):
        return False
    d = 2
    while not L.lt(n, L.mul(d, d)):
        L.tick("loop_iterations")
        L.tick("trial_divisors")
        if L.eq(L.mod(n, d), 0):
            return False
        d = L.add(d, 1)
    return True


def mod_power(a, exponent, modulus, L):
    L.tick("modular_power_calls")
    L.require(not L.lt(exponent, 0), "negative modular exponent")
    base, result = L.mod(a, modulus), 1
    while not L.eq(exponent, 0):
        L.tick("loop_iterations")
        L.tick("exponent_bits")
        if not L.eq(L.bit(exponent), 0):
            result = L.mod(L.mul(result, base), modulus)
        exponent = L.shift(exponent)
        if not L.eq(exponent, 0):
            base = L.mod(L.mul(base, base), modulus)
    return result


class Field:
    def __init__(self, p, L):
        self.p, self.L = p, L

    def reduce(self, a):
        self.L.tick("field_reductions")
        return a % self.p

    def add(self, a, b):
        self.L.tick("field_adds")
        return self.reduce(a + b)

    def sub(self, a, b):
        self.L.tick("field_subs")
        return self.reduce(a - b)

    def mul(self, a, b):
        self.L.tick("field_muls")
        return self.reduce(a * b)

    def power(self, a, exponent):
        L = self.L
        L.tick("field_power_calls")
        base, result = self.reduce(a), 1
        while not L.eq(exponent, 0):
            L.tick("loop_iterations")
            L.tick("exponent_bits")
            if not L.eq(L.bit(exponent), 0):
                result = self.mul(result, base)
            exponent = L.shift(exponent)
            if not L.eq(exponent, 0):
                base = self.mul(base, base)
        return result

    def inverse(self, a):
        L = self.L
        L.tick("field_inverse_calls")
        L.require(not L.eq(a, 0), "inverse of zero")
        result = self.power(a, L.sub(self.p, 2))
        L.require(L.eq(self.mul(a, result), 1), "inverse verification failed")
        return result


class Curve:
    def __init__(self, p, a, b, L):
        self.p, self.a, self.b, self.L = p, a, b, L
        self.f = Field(p, L)

    def rhs(self, x):
        f = self.f
        return f.add(f.add(f.mul(f.mul(x, x), x), f.mul(self.a, x)), self.b)

    def check_point(self, point):
        L, f = self.L, self.f
        L.tick("point_membership_checks")
        L.require(not L.eq(point, None), "expected an affine point")
        x, y = point
        L.require(not L.lt(x, 0) and L.lt(x, self.p), "noncanonical x")
        L.require(not L.lt(y, 0) and L.lt(y, self.p), "noncanonical y")
        L.require(L.eq(f.mul(y, y), self.rhs(x)), "point off curve")

    def negate(self, point):
        self.L.tick("group_negations")
        if self.L.eq(point, None):
            return None
        x, y = point
        return x, self.f.sub(0, y)

    def add(self, left, right):
        L, f = self.L, self.f
        L.tick("group_additions")
        if L.eq(left, None):
            return right
        if L.eq(right, None):
            return left
        x, y = left
        u, v = right
        if L.eq(x, u):
            if L.eq(f.add(y, v), 0):
                return None
            L.require(L.eq(y, v), "inconsistent equal-abscissa points")
            num = f.add(f.mul(3, f.mul(x, x)), self.a)
            den = f.mul(2, y)
        else:
            num, den = f.sub(v, y), f.sub(u, x)
        slope = f.mul(num, f.inverse(den))
        xx = f.sub(f.sub(f.mul(slope, slope), x), u)
        yy = f.sub(f.mul(slope, f.sub(x, xx)), y)
        return xx, yy


def zadd(x, y, L):
    a, b = x
    c, d = y
    return L.add(a, c), L.add(b, d)


def zneg(x, L):
    a, b = x
    return L.neg(a), L.neg(b)


def zconj(x, L):
    a, b = x
    return L.add(a, b), L.neg(b)


def zmul(x, y, L):
    a, b = x
    c, d = y
    ac, bd, ad, bc = L.mul(a, c), L.mul(b, d), L.mul(a, d), L.mul(b, c)
    return L.sub(ac, bd), L.add(L.add(ad, bc), bd)


def znorm(x, L):
    a, b = x
    return L.add(L.add(L.mul(a, a), L.mul(a, b)), L.mul(b, b))


class Character:
    def __init__(self, q, L, prefix, report):
        self.q, self.L = q, L
        self.values = Vector(L, prefix + "/character_values")
        divisors = Vector(L, prefix + "/prime_divisors_q_minus_1")
        remaining = L.sub(q, 1)
        self.h, rem = L.divmod(remaining, 6)
        L.require(L.eq(rem, 0), "six does not divide q-1")
        L.require(L.eq(L.mod(self.h, 2), 1), "character exponent is not odd")
        d = 2
        while not L.lt(remaining, L.mul(d, d)):
            L.tick("loop_iterations")
            L.tick("factor_trial_divisors")
            if L.eq(L.mod(remaining, d), 0):
                divisors.append(d)
                while L.eq(L.mod(remaining, d), 0):
                    L.tick("loop_iterations")
                    remaining, rem = L.divmod(remaining, d)
                    L.require(L.eq(rem, 0), "factor division remainder")
            d = L.add(d, 1)
        if L.lt(1, remaining):
            divisors.append(remaining)
        report["prime_divisors_q_minus_1"] = []
        for i in range(divisors.length()):
            L.tick("loop_iterations")
            report["prime_divisors_q_minus_1"].append(divisors.get(i))
        g = 2
        report["primitive_generator_candidates"] = []
        while L.lt(g, q):
            L.tick("loop_iterations")
            L.tick("primitive_generator_candidates")
            trial = {"g": g, "tests": [], "complete": False}
            report["primitive_generator_candidates"].append(trial)
            valid = True
            for i in range(divisors.length()):
                L.tick("loop_iterations")
                ell = divisors.get(i)
                exponent, rem = L.divmod(L.sub(q, 1), ell)
                L.require(L.eq(rem, 0), "primitive-generator exponent remainder")
                result = mod_power(g, exponent, q, L)
                trial["tests"].append({"prime_divisor": ell, "value": result})
                if L.eq(result, 1):
                    valid = False
                    break
            trial["complete"], trial["accepted"] = True, valid
            if valid:
                break
            g = L.add(g, 1)
        L.require(L.lt(g, q), "no primitive scalar generator")
        self.g, self.z = g, mod_power(g, self.h, q, L)
        self.phases = Table(L, prefix + "/six_phase_map")
        residue = 1
        for j in range(6):
            L.tick("loop_iterations")
            phase = L.fixed_read(ZETA_POWERS, j)
            self.phases.put_new(residue, phase)
            residue = L.mod(L.mul(residue, self.z), q)
        L.require(L.eq(residue, 1), "sixth power did not return to one")
        L.require(L.eq(self.phases.length(), 6), "sixth roots not distinct")
        report.update({"g": g, "h": self.h, "z": self.z})
        for n in range(q):
            L.tick("loop_iterations")
            self.values.append(self.evaluate(n))
        L.require(L.eq(self.values.get(L.sub(q, 1)), (-1, 0)), "chi(-1) != -1")
        L.require(L.eq(self.evaluate(g), (0, 1)), "chi(g) != zeta")
        report["chi_g_verified"] = True

    def evaluate(self, value):
        L = self.L
        L.tick("character_evaluations")
        n = L.mod(value, self.q)
        if L.eq(n, 0):
            return 0, 0
        residue = mod_power(n, self.h, self.q, L)
        phase = self.phases.get(residue)
        L.require(not L.eq(phase, MISSING), "character value outside sixth roots")
        return phase


class PRNG:
    """LCG32: state <- (1664525*state+1013904223) mod 2^32.

    Each output word is state XOR (state >> 16), a fixed bijection of 32-bit
    words. randbelow uses rejection below 2^32-(2^32 mod bound). Orientations
    use below(2) on a NEW output. No statistical independence claim is made.
    """
    MODULUS = 4294967296

    def __init__(self, seed, L):
        self.L = L
        L.tick("prng_initializations")
        self.state = L.mod(seed, self.MODULUS)

    def draw(self):
        L = self.L
        L.tick("prng_draws")
        self.state = L.mod(L.add(L.mul(1664525, self.state), 1013904223), self.MODULUS)
        return L.xor(self.state, L.shift(self.state, 16))

    def below(self, bound):
        L = self.L
        L.require(L.lt(0, bound) and not L.lt(self.MODULUS, bound), "PRNG bound")
        limit = L.sub(self.MODULUS, L.mod(self.MODULUS, bound))
        while True:
            L.tick("loop_iterations")
            value = self.draw()
            if L.lt(value, limit):
                return L.mod(value, bound)
            L.tick("prng_rejections")

    def orientation(self):
        self.L.tick("prng_orientation_bits")
        return self.below(2)


def square_roots(p, L, prefix):
    roots, f = Vector(L, prefix + "/square_roots"), Field(p, L)
    for residue in range(p):
        L.tick("loop_iterations")
        roots.append(Vector(L, prefix + "/roots/" + str(residue)))
    for y in range(p):
        L.tick("loop_iterations")
        roots.get(f.mul(y, y)).append(y)
    return roots


def center(t, p, half, L):
    if L.lt(half, t):
        return L.sub(t, p)
    return t


def sign(t, L):
    if L.lt(0, t):
        return 1
    if L.lt(t, 0):
        return -1
    return 0


def public_features(curve, points, character, L, prefix, report):
    cache = Table(L, prefix + "/feature_cache")
    half, _ = L.divmod(curve.p, 2)
    report["feature_rows"] = []
    cache.put_new(None, ((0, 0), (0, 0), (0, 0)))
    for i in range(points.length()):
        L.tick("loop_iterations")
        point = points.get(i)
        x, y = point
        row = {"point": point, "complete": False}
        report["feature_rows"].append(row)
        L.phase = prefix + "/feature/sign"
        fsign = (sign(center(y, curve.p, half, L), L), 0)
        row["sign"] = fsign
        L.phase = prefix + "/feature/formal_parameter"
        parameter = curve.f.mul(curve.f.sub(0, x), curve.f.inverse(y))
        centered = center(parameter, curve.p, half, L)
        fpar = character.evaluate(L.mod(centered, character.q))
        row.update({"parameter_mod_p": parameter, "centered_parameter": centered, "par": fpar})
        L.phase = prefix + "/feature/even_control"
        even = (sign(center(x, curve.p, half, L), L), 0)
        row["even"] = even
        L.phase = prefix + "/feature/cache_write"
        cache.put_new(point, (fsign, fpar, even))
        row["complete"] = True
    L.phase = prefix + "/feature/symmetry_checks"
    for i in range(points.length()):
        L.tick("loop_iterations")
        point = points.get(i)
        opposite = curve.negate(point)
        fs, fp, fe = cache.get(point)
        ns, np, ne = cache.get(opposite)
        L.require(L.eq(ns, zneg(fs, L)), "sign feature not odd")
        L.require(L.eq(np, zneg(fp, L)), "parameter feature not odd")
        L.require(L.eq(ne, fe), "even feature not even")
    report["feature_symmetry_verified"] = True
    return cache


def certify_orbit(curve, generator, q, enumerated, points, L, prefix, report):
    orbit, seen = Vector(L, prefix + "/points"), Table(L, prefix + "/seen")
    current = None
    report.update({"generator": generator, "orbit_rows": [], "orbit_complete": False})
    for n in range(1, L.add(q, 1)):
        L.tick("loop_iterations")
        row = {"n": n, "complete": False}
        report["orbit_rows"].append(row)
        current = curve.add(current, generator)
        row["point"] = current
        if L.eq(n, q):
            L.require(L.eq(current, None), "orbit does not close at q")
        else:
            L.require(not L.eq(current, None), "orbit closes before q")
            curve.check_point(current)
            L.require(L.eq(enumerated.get(current), True), "orbit point absent from enumeration")
            seen.put_new(current, True)
            orbit.append(current)
        row["complete"] = True
    L.require(L.eq(seen.length(), L.sub(q, 1)), "wrong orbit cardinality")
    for i in range(points.length()):
        L.tick("loop_iterations")
        L.require(L.eq(seen.get(points.get(i)), True), "enumerated point missing from orbit")
    report["orbit_complete"] = True
    return orbit


def measure(orbit, cache, planted, character, L, report):
    sums = ((0, 0), (0, 0), (0, 0), (0, 0))
    zeros = (0, 0, 0, 0)
    report["measurement_rows"] = []
    report["measurement_complete"] = False
    for i in range(orbit.length()):
        L.tick("loop_iterations")
        point = orbit.get(i)
        fs, fp, fe = cache.get(point)
        plant = planted.get(point)
        L.require(not L.eq(plant, MISSING), "missing planted point value")
        n = L.add(i, 1)
        chi = character.values.get(n)
        weight = zconj(chi, L)
        values = (fs, fp, fe, plant)
        new_sums, new_zeros = [], []
        row = {"n": n, "point": point, "chi": chi, "features": values,
               "accumulated_feature_prefix": [], "complete": False}
        report["measurement_rows"].append(row)
        for j in range(4):
            L.tick("loop_iterations")
            # These are four-element arithmetic records, not indexed data caches.
            new_sums.append(zadd(sums[j], zmul(values[j], weight, L), L))
            new_zeros.append(L.add(zeros[j], 1) if L.eq(values[j], (0, 0)) else zeros[j])
            row["accumulated_feature_prefix"] = list(new_sums)
        sums, zeros = tuple(new_sums), tuple(new_zeros)
        report["partial_sums"], report["zero_counts"] = sums, zeros
        row["complete"] = True
    denominator = L.sub(character.q, 1)
    den2 = L.mul(denominator, denominator)
    report["sums"] = []
    for j in range(4):
        L.tick("loop_iterations")
        report["sums"].append({"pair": sums[j], "denominator": denominator,
                               "squared_magnitude_numerator": znorm(sums[j], L),
                               "squared_magnitude_denominator": den2})
    report["feature_order"] = ["sign", "par", "even", "planted"]
    report["measurement_complete"] = True
    return sums


def null_reference(points, cache, q, L, report):
    energies = (0, 0)
    for i in range(points.length()):
        L.tick("loop_iterations")
        fs, fp, _ = cache.get(points.get(i))
        energies = (L.add(energies[0], znorm(fs, L)),
                    L.add(energies[1], znorm(fp, L)))
        report["partial_feature_energies"] = energies
    denominator = L.sub(q, 1)
    den2 = L.mul(denominator, denominator)
    numerators = (L.mul(2, energies[0]), L.mul(2, energies[1]))
    report["ideal_signed_pair_null"] = {
        "feature_order": ["sign", "par"], "mean": (0, 0),
        "energy_sums": energies, "second_moment_numerators": numerators,
        "second_moment_denominator": den2,
        "model": "Separate ideal uniform signed-pair permutation model; not an LCG theorem",
        "flag": "Strict squared correlation > 9 times ideal second moment; descriptive only",
    }
    return numerators


def descriptive_flags(sums, null_numerators, L):
    flags = []
    for j in range(2):
        L.tick("loop_iterations")
        flags.append(L.lt(L.mul(9, null_numerators[j]), znorm(sums[j], L)))
    return flags


def permutation_control(seed, orbit, cache, character, null_numerators, L, prefix, report):
    q = character.q
    half, remainder = L.divmod(L.sub(q, 1), 2)
    L.require(L.eq(remainder, 0), "odd order expected for pair permutation")
    rng = PRNG(seed, L)
    report.update({"seed": seed, "assignments": [], "rows": [], "complete": False,
                   "shuffle_complete": False})
    representatives = Vector(L, prefix + "/representatives")
    labels = Vector(L, prefix + "/signed_labels")
    for n in range(1, L.add(half, 1)):
        L.tick("loop_iterations")
        representatives.append(n)
    for n in range(q):
        L.tick("loop_iterations")
        labels.append(0)
    i = L.sub(half, 1)
    while L.lt(0, i):
        L.tick("loop_iterations")
        report["shuffle_current_index"] = i
        j = rng.below(L.add(i, 1))
        left, right = representatives.get(i), representatives.get(j)
        L.tick("fisher_yates_swaps")
        representatives.put(i, right)
        representatives.put(j, left)
        i = L.sub(i, 1)
    report["shuffle_complete"] = True
    for n in range(1, L.add(half, 1)):
        L.tick("loop_iterations")
        representative = representatives.get(L.sub(n, 1))
        orientation = rng.orientation()
        label = representative if L.eq(orientation, 0) else L.sub(q, representative)
        opposite = L.sub(q, label)
        labels.put(n, label)
        labels.put(L.sub(q, n), opposite)
        report["assignments"].append({"n": n, "representative": representative,
                                       "orientation": orientation, "label": label,
                                       "opposite_label": opposite})
    seen = Table(L, prefix + "/permutation_seen")
    for n in range(1, q):
        L.tick("loop_iterations")
        label = labels.get(n)
        L.require(L.lt(0, label) and L.lt(label, q), "invalid permuted label")
        L.require(L.eq(labels.get(L.sub(q, n)), L.sub(q, label)), "pair oddness lost")
        seen.put_new(label, True)
    L.require(L.eq(seen.length(), L.sub(q, 1)), "permutation is not bijective")
    sums, zeros = ((0, 0), (0, 0)), (0, 0)
    for i in range(orbit.length()):
        L.tick("loop_iterations")
        point = orbit.get(i)
        fs, fp, _ = cache.get(point)
        n = L.add(i, 1)
        label = labels.get(n)
        weight = zconj(character.values.get(label), L)
        row = {"n": n, "point": point, "assigned_label": label, "complete": False}
        report["rows"].append(row)
        sums = (zadd(sums[0], zmul(fs, weight, L), L),
                zadd(sums[1], zmul(fp, weight, L), L))
        zeros = (L.add(zeros[0], 1) if L.eq(fs, (0, 0)) else zeros[0],
                 L.add(zeros[1], 1) if L.eq(fp, (0, 0)) else zeros[1])
        report["partial_sums"], report["zero_counts"] = sums, zeros
        row["complete"] = True
    denominator = L.sub(q, 1)
    den2 = L.mul(denominator, denominator)
    report["sums"] = []
    for j in range(2):
        L.tick("loop_iterations")
        report["sums"].append({"pair": sums[j], "denominator": denominator,
                               "squared_magnitude_numerator": znorm(sums[j], L),
                               "squared_magnitude_denominator": den2})
    report["feature_order"] = ["sign", "par"]
    report["descriptive_above_3_rms"] = descriptive_flags(sums, null_numerators, L)
    report["complete"] = True


def run_field(p, L, report):
    prefix = "p" + str(p)
    report.update({"p": p, "status": "IN_PROGRESS", "candidates": [],
                   "candidate_count": 0})
    L.phase = prefix + "/field_certification"
    L.require(prime(p, L), "frozen field modulus is not prime")
    L.phase = prefix + "/square_root_setup"
    roots = square_roots(p, L, prefix)
    count, chosen, q = 0, None, None
    L.phase = prefix + "/curve_admission"
    for a in range(1, p):
        L.tick("loop_iterations")
        if not L.lt(count, CANDIDATE_LIMIT):
            break
        for b in range(1, p):
            L.tick("loop_iterations")
            if not L.lt(count, CANDIDATE_LIMIT):
                break
            count = L.add(count, 1)
            L.tick("curve_candidates")
            report["candidate_count"] = count
            candidate = {"index": count, "a": a, "b": b, "status": "IN_PROGRESS"}
            report["candidates"].append(candidate)
            curve = Curve(p, a, b, L)
            f = curve.f
            disc = f.add(f.mul(4, f.mul(f.mul(a, a), a)), f.mul(27, f.mul(b, b)))
            candidate["discriminant_expression"] = disc
            if L.eq(disc, 0):
                candidate["status"] = "SINGULAR"
                continue
            order = 1
            for x in range(p):
                L.tick("loop_iterations")
                order = L.add(order, roots.get(curve.rhs(x)).length())
                candidate["partial_point_count"] = order
                candidate["x_counted"] = L.add(x, 1)
            candidate["q"] = order
            # The full count is paid for every nonsingular candidate. Cheap
            # eligibility tests precede primality; skipped tests are disclosed.
            if L.eq(order, p):
                candidate["status"] = "ANOMALOUS"
                continue
            if not L.eq(L.mod(order, 12), 7):
                candidate["status"] = "ORDER_CONGRUENCE_REJECTED"
                continue
            candidate["prime_tested"] = True
            if not prime(order, L):
                candidate["status"] = "COMPOSITE_ORDER"
                continue
            chosen, q = curve, order
            candidate["status"] = "ADMITTED"
            break
        if not L.eq(chosen, None):
            break
    if L.eq(chosen, None):
        report.update({"status": "INCOMPLETE", "reason": "No admitted curve in frozen candidate window"})
        return False
    report.update({"a": chosen.a, "b": chosen.b, "q": q})
    L.phase = prefix + "/independent_point_enumeration"
    points, enumerated = Vector(L, prefix + "/enumerated_points"), Table(L, prefix + "/enumerated_membership")
    report["enumerated_points"] = []
    for x in range(p):
        L.tick("loop_iterations")
        ys = roots.get(chosen.rhs(x))
        for j in range(ys.length()):
            L.tick("loop_iterations")
            y = ys.get(j)
            point = (x, y)
            chosen.check_point(point)
            L.require(not L.eq(y, 0), "odd-order curve has affine 2-torsion")
            points.append(point)
            enumerated.put_new(point, True)
            report["enumerated_points"].append(point)
    L.require(L.eq(L.add(points.length(), 1), q), "independent enumeration/order mismatch")
    g0 = points.get(0)  # x and the root lists were generated in increasing order.
    report["G0"] = g0
    L.phase = prefix + "/character_setup"
    report["character"] = {}
    character = Character(q, L, prefix, report["character"])
    L.phase = prefix + "/feature/cache_setup"
    cache = public_features(chosen, points, character, L, prefix, report)
    L.phase = prefix + "/ideal_null_reference"
    null_numerators = null_reference(points, cache, q, L, report)
    L.phase = prefix + "/generator_setup"
    generators = Vector(L, prefix + "/generators")
    generators.append(g0)
    generators.append(chosen.add(g0, g0))
    generators.append(chosen.negate(g0))
    planted = Table(L, prefix + "/planted_control")
    planted.put_new(None, (0, 0))
    all_sums, g0_orbit = None, None
    report["generators"] = []
    generator_names = ("G0", "2G0", "-G0")
    for j in range(3):
        L.tick("loop_iterations")
        name = L.fixed_read(generator_names, j)
        generator = generators.get(j)
        L.require(not L.eq(generator, None), "identity diagnostic generator")
        greport = {"name": name}
        report["generators"].append(greport)
        oprefix = prefix + "/orbit/" + name
        L.phase = oprefix + "/certification"
        orbit = certify_orbit(chosen, generator, q, enumerated, points, L, oprefix, greport)
        if L.eq(j, 0):
            g0_orbit = orbit
            L.phase = prefix + "/planted_control_setup"
            for i in range(orbit.length()):
                L.tick("loop_iterations")
                planted.put_new(orbit.get(i), character.values.get(L.add(i, 1)))
        L.phase = oprefix + "/cached_measurements"
        sums = measure(orbit, cache, planted, character, L, greport)
        greport["descriptive_above_3_rms"] = descriptive_flags(sums, null_numerators, L)
        L.phase = oprefix + "/exact_control_checks"
        L.require(L.eq(sums[2], (0, 0)), "even control correlation is nonzero")
        if L.eq(j, 0):
            all_sums = sums
            L.require(L.eq(sums[3], (L.sub(q, 1), 0)), "planted G0 correlation failed")
        elif L.eq(j, 1):
            chi2 = character.values.get(2)
            for k in range(4):
                L.tick("loop_iterations")
                L.require(L.eq(sums[k], zmul(chi2, all_sums[k], L)), "2G0 covariance failed")
            expected = zmul((L.sub(q, 1), 0), chi2, L)
            L.require(L.eq(sums[3], expected), "planted 2G0 correlation failed")
        else:
            for k in range(4):
                L.tick("loop_iterations")
                L.require(L.eq(sums[k], zneg(all_sums[k], L)), "-G0 covariance failed")
            L.require(L.eq(sums[3], (L.neg(L.sub(q, 1)), 0)), "planted -G0 correlation failed")
        greport["exact_controls_verified"] = True
    report["permutations"] = []
    for i in range(3):
        L.tick("loop_iterations")
        seed = L.fixed_read(SEEDS, i)
        preport = {"seed": seed, "complete": False}
        report["permutations"].append(preport)
        pprefix = prefix + "/signed_permutation/" + str(seed)
        L.phase = pprefix
        permutation_control(seed, g0_orbit, cache, character, null_numerators, L, pprefix, preport)
    report["status"] = "COMPLETE"
    return True


def main():
    L = Ledger()
    result = {"protocol": "H014/protocol.md", "status": "IN_PROGRESS", "fields": [],
              "verified_ecdlp_improvement": "NONE", "solver": False,
              "caps": {"events": MAX_EVENTS, "seconds": MAX_SECONDS},
              "prng": {"name": "LCG32", "multiplier": 1664525, "increment": 1013904223,
                       "modulus": 4294967296, "output_word": "state XOR (state >> 16)",
                       "orientation": "fresh rejection draw with bound 2",
                       "seeds_per_curve": SEEDS, "iid_claim": False},
              "accounting": {"kind": "nested abstract events, not bit cost or throughput",
                             "source_docstring_defines_exclusions": True,
                             "final_hashing_and_serialization_outside_timer": True,
                             "storage_unit": "retained algorithm vector/dictionary entries, not bytes",
                             "fixed_size_arithmetic_records_excluded_from_storage": True}}
    completed, incomplete = 0, 0
    try:
        for i in range(3):
            L.tick("loop_iterations")
            p = L.fixed_read(FIELDS, i)
            field_report = {"p": p, "status": "IN_PROGRESS"}
            result["fields"].append(field_report)
            if run_field(p, L, field_report):
                completed = L.add(completed, 1)
            else:
                incomplete = L.add(incomplete, 1)
        L.phase = "completion"
        result["status"] = "COMPLETE" if L.eq(incomplete, 0) else "INCOMPLETE"
        L.tick("completion_checks")
    except BudgetStop as exc:
        result["status"], result["stop_reason"] = "BUDGET_STOP", str(exc)
    except CorrectnessFailure as exc:
        result["status"], result["stop_reason"] = "CORRECTNESS_FAILURE", str(exc)
    except Exception as exc:
        result["status"] = "INTERNAL_ERROR"
        result["stop_reason"] = type(exc).__name__ + ": " + str(exc)
    # Only diagnostic output/bookkeeping follows; it does not resume arithmetic.
    elapsed = time.monotonic() - L.started
    # A cap may fire in the charged counter increment after a field has already
    # finished. Derive output counters from retained terminal field statuses.
    # This is reporting-only metadata, never fed back into the computation.
    result.update({"completed_fields": sum(f["status"] == "COMPLETE" for f in result["fields"]),
                   "admission_incomplete_fields": sum(f["status"] == "INCOMPLETE" for f in result["fields"]),
                   "stopped_phase": L.phase, "instrumented_events": L.total,
                   "elapsed_arithmetic_seconds": elapsed,
                   "category_counts": dict(L.categories),
                   "phase_category_counts": {name: dict(counts) for name, counts in L.phases.items()},
                   "algorithm_storage_entries": L.storage_entries,
                   "peak_algorithm_storage_entries": L.peak_entries,
                   "storage_entries_by_table": dict(L.storage)})
    result["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
