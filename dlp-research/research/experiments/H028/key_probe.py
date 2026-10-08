#!/usr/bin/env python3
"""H028 frozen finite correctness/accounting diagnostic. Execution needs approval.

Only --execute runs numerical work. H018 support is loaded inside execute(); its
global caps are changed BEFORE Meter construction. No solver uses the diagnostic
orbit table. Field operations are modular-RAM primitives, NOT bit/hardware costs.
Powers/inverses, affine arithmetic, polynomial products, hashing/probing, loops,
indices and dynamic accesses are expanded and metered. Fixed-schema attributes,
register assignments, instrumentation, hashes and JSON are administrative; their
wall time is included. Completed records plus pending markers survive interruption.

Polynomial reference uses actual numerator/denominator products in Fp[x,y],
y^2=x^3+A*x+B. It never accumulates slopes as Laurent coefficients. The ordinary
binary reference DOES accumulate slopes, independently of orbit propagation.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parent
SUPPORT = HERE.parent / "H018" / "bm_probe.py"
PROTOCOL = HERE / "protocol.md"
EVENT_CAP = 10_000_000
SECONDS_CAP = 55.0
FIXTURES = ((59, 28, 27, 73, 34, 35, 13, 10),
            (101, 2, 31, 103, 0, 43, 15, 10),
            (251, 1, 4, 271, 0, 2, 24, 20),
            (8191, 1, 5, 8053, 0, 789, 127, 70))
SEEDS = (7, 19, 43)


class Failure(Exception):
    pass


@dataclass(frozen=True)
class Point:
    x: int
    y: int


@dataclass(frozen=True)
class Archive:
    x: int | None
    h: int


def need(condition, message):
    if not condition:
        raise Failure(message)


def length(m, values):
    m.tick("array_length")
    return len(values)


def put(m, record, key, value):
    m.tick("trace_field")
    record[key] = value


def pending(m, record, operation, **fields):
    # Attach before charging, so a cap here still identifies unfinished work.
    record["pending"] = {"operation": operation, **fields}
    m.tick("trace_field", len(fields) + 1)


def done(m, record):
    m.tick("trace_field")
    record["pending"] = None


def point_record(m, point):
    if m.eq(point, None):
        return m.record(infinity=True)
    return m.record(infinity=False, x=point.x, y=point.y)


def canonical(m, f, h):
    negative = f.sub(0, h)
    if m.lt(negative, h):
        return negative, -1
    return h, 1


class CountedField:
    """Expand inverses in the RAM ledger; retain their symbolic boundary too.

    Projection subtracts their *observed paid* M/S expansion before assigning
    I=8M, avoiding double counting. Counter snapshots are instrumentation only.
    """
    def __init__(self, field, meter):
        self.field, self.m = field, meter
        self.inverse_by_phase = {}

    def __getattr__(self, name):
        return getattr(self.field, name)

    def inverse(self, value):
        phase = self.m.phase
        before_m = self.m.by_kind.get("field_mul", 0)
        before_s = self.m.by_kind.get("field_square", 0)
        result = self.field.inverse(value)
        row = self.inverse_by_phase.setdefault(phase, [0, 0, 0])
        row[0] += 1
        row[1] += self.m.by_kind.get("field_mul", 0) - before_m
        row[2] += self.m.by_kind.get("field_square", 0) - before_s
        return result


class Curve:
    def __init__(self, base, m, p, a, b, q):
        self.m, self.f = m, CountedField(base.Field(m, p), m)
        self.p, self.a, self.b, self.q = p, a, b, q

    def equal(self, p, q):
        m = self.m
        if m.eq(p, None):
            return m.eq(q, None)
        if m.eq(q, None):
            return False
        return m.eq(p.x, q.x) and m.eq(p.y, q.y)

    def neg(self, p):
        if self.m.eq(p, None):
            return None
        return Point(p.x, self.f.sub(0, p.y))

    def check(self, p):
        m, f = self.m, self.f
        if m.eq(p, None):
            return
        rhs = f.add(f.add(f.mul(f.square(p.x), p.x), f.mul(self.a, p.x)), self.b)
        need(m.eq(f.square(p.y), rhs), "point equation failed")

    def add(self, p, q):
        """Independent ordinary affine operation; returns point,slope,kind."""
        m, f = self.m, self.f
        if m.eq(p, None):
            return q, None, "identity_left"
        if m.eq(q, None):
            return p, None, "identity_right"
        if m.eq(p.x, q.x):
            if m.eq(f.add(p.y, q.y), 0):
                return None, None, "vertical"
            need(m.eq(p.y, q.y), "invalid equal-x inputs")
            numerator = f.add(f.mul(3, f.square(p.x)), self.a)
            denominator = f.mul(2, p.y)
            kind = "tangent"
        else:
            numerator = f.sub(q.y, p.y)
            denominator = f.sub(q.x, p.x)
            kind = "regular"
        slope = f.mul(numerator, f.inverse(denominator))
        x = f.sub(f.sub(f.square(slope), p.x), q.x)
        y = f.sub(f.mul(slope, f.sub(p.x, x)), p.y)
        return Point(x, y), slope, kind

    def scalar(self, n, p):
        m = self.m
        need(not m.lt(n, 0), "negative scalar")
        result = None
        while not m.eq(n, 0):
            if not m.eq(m.band(n, 1), 0):
                result, _, _ = self.add(result, p)
            n = m.shr(n, 1)
            if not m.eq(n, 0):
                p, _, _ = self.add(p, p)
        return result

    def add_h(self, p, hp, q, hq):
        m, f = self.m, self.f
        result, slope, kind = self.add(p, q)
        if m.eq(kind, "identity_left"):
            return result, hq, kind
        if m.eq(kind, "identity_right"):
            return result, hp, kind
        if m.eq(kind, "vertical"):
            need(m.eq(f.add(hp, hq), 0), "vertical h sum failed")
            return result, 0, kind
        return result, f.sub(f.add(hp, hq), slope), kind

    def scalar_h(self, n, p, hp):
        m = self.m
        result, hr = None, 0
        while not m.eq(n, 0):
            if not m.eq(m.band(n, 1), 0):
                result, hr, _ = self.add_h(result, hr, p, hp)
            n = m.shr(n, 1)
            if not m.eq(n, 0):
                p, hp, _ = self.add_h(p, hp, p, hp)
        return result, hr


def bits(m, n):
    result = []
    while not m.eq(n, 0):
        m.append(result, m.band(n, 1))
        n = m.shr(n, 1)
    return result


def binary_h(curve, p, owner, name):
    """A separate q-Miller chain, never calling add_h or orbit propagation."""
    m, f = curve.m, curve.f
    trace = {"name": name, "steps": [], "completed": False, "pending": None}
    m.append(owner, trace)
    m.tick("trace_field", 4)
    if m.eq(p, None):
        put(m, trace, "h", 0)
        put(m, trace, "completed", True)
        return 0
    digits = bits(m, curve.q)
    u, coefficient = None, 0
    j = m.sub(length(m, digits), 1)
    while m.le(0, j):
        pending(m, trace, "binary_miller_bit", bit_index=j)
        u, slope, kind = curve.add(u, u)
        coefficient = f.add(coefficient, coefficient)
        if not m.eq(slope, None):
            coefficient = f.add(coefficient, slope)
        double_kind = kind
        digit = m.read(digits, j)
        if not m.eq(digit, 0):
            u, slope, kind = curve.add(u, p)
            if not m.eq(slope, None):
                coefficient = f.add(coefficient, slope)
        else:
            kind = "no_add"
        m.append(trace["steps"], m.record(bit_index=j, digit=digit,
                 double_kind=double_kind, add_kind=kind, coefficient=coefficient,
                 point=point_record(m, u)))
        done(m, trace)
        j = m.sub(j, 1)
    need(m.eq(u, None), "Miller chain did not end at infinity")
    qfield = m.rem(curve.q, curve.p)
    h = f.mul(coefficient, f.inverse(qfield))
    put(m, trace, "first_coefficient", coefficient)
    put(m, trace, "h", h)
    put(m, trace, "completed", True)
    return h


def poly_trim(m, a):
    while m.lt(1, length(m, a)):
        last = m.sub(length(m, a), 1)
        if not m.eq(m.read(a, last), 0):
            break
        m.tick("array_pop")
        a.pop()
    return a


def poly_add(m, f, a, b):
    na, nb = length(m, a), length(m, b)
    n = nb if m.lt(na, nb) else na
    out = m.zeroes(n)
    i = 0
    while m.lt(i, n):
        x = m.read(a, i) if m.lt(i, na) else 0
        y = m.read(b, i) if m.lt(i, nb) else 0
        m.write(out, i, f.add(x, y))
        i = m.add(i, 1)
    return poly_trim(m, out)


def poly_mul(m, f, a, b):
    na, nb = length(m, a), length(m, b)
    out = m.zeroes(m.sub(m.add(na, nb), 1))
    i = 0
    while m.lt(i, na):
        x = m.read(a, i)
        j = 0
        while m.lt(j, nb):
            y = m.read(b, j)
            if not m.eq(x, 0) and not m.eq(y, 0):
                ij = m.add(i, j)
                m.write(out, ij, f.add(m.read(out, ij), f.mul(x, y)))
            j = m.add(j, 1)
        i = m.add(i, 1)
    return poly_trim(m, out)


def ring_mul(curve, left, right):
    m, f = curve.m, curve.f
    a, b = left
    c, d = right
    ac, bd = poly_mul(m, f, a, c), poly_mul(m, f, b, d)
    cubic = []
    m.append(cubic, curve.b)
    m.append(cubic, curve.a)
    m.append(cubic, 0)
    m.append(cubic, 1)
    even = poly_add(m, f, ac, poly_mul(m, f, bd, cubic))
    odd = poly_add(m, f, poly_mul(m, f, a, d), poly_mul(m, f, b, c))
    return even, odd


def ring_constant(m, value):
    a, b = [], []
    m.append(a, value)
    m.append(b, 0)
    return a, b


def line_factors(curve, p, r, result, slope, kind):
    m, f = curve.m, curve.f
    if m.eq(kind, "identity_left") or m.eq(kind, "identity_right"):
        return ring_constant(m, 1), ring_constant(m, 1)
    if m.eq(kind, "vertical"):
        a, b = [], []
        m.append(a, f.sub(0, p.x)); m.append(a, 1); m.append(b, 0)
        return (a, b), ring_constant(m, 1)
    # Actual line y-slope*x-intercept and actual vertical x-x(result).
    intercept = f.sub(p.y, f.mul(slope, p.x))
    a, b, c, d = [], [], [], []
    m.append(a, f.sub(0, intercept)); m.append(a, f.sub(0, slope)); m.append(b, 1)
    m.append(c, f.sub(0, result.x)); m.append(c, 1); m.append(d, 0)
    return (a, b), (c, d)


def leading_pair(curve, value):
    """x^i starts z^-2i; x^i*y starts -z^-(2i+3).

    Their next corrections are >=4 exponents later on a short model. Even/odd
    leading exponents cannot cancel. Scan both polynomials to get the two top
    Laurent coefficients; no slope/coefficient-chain input is used here.
    """
    m, f = curve.m, curve.f
    top, lc, following = -1, 0, 0
    component = 0
    while m.lt(component, 2):
        pol = m.read(value, component)
        j = 0
        while m.lt(j, length(m, pol)):
            coefficient = m.read(pol, j)
            exponent = m.mul(2, j)
            if m.eq(component, 1):
                exponent = m.add(exponent, 3)
                coefficient = f.sub(0, coefficient)
            if not m.eq(coefficient, 0):
                if m.lt(top, exponent):
                    following = lc if m.eq(top, m.sub(exponent, 1)) else 0
                    top, lc = exponent, coefficient
                elif m.eq(exponent, m.sub(top, 1)):
                    following = coefficient
            j = m.add(j, 1)
        component = m.add(component, 1)
    need(not m.eq(lc, 0), "zero Miller polynomial")
    return top, lc, following


def polynomial_miller(curve, g, hg, owner):
    m, f = curve.m, curve.f
    report = {"completed": False, "pending": None, "steps": []}
    owner["polynomial_miller"] = report
    m.tick("trace_field", 4)
    numerator, denominator = ring_constant(m, 1), ring_constant(m, 1)
    report["current_numerator"], report["current_denominator"] = numerator, denominator
    m.tick("trace_field", 2)
    u = None
    digits = bits(m, curve.q)
    j = m.sub(length(m, digits), 1)
    while m.le(0, j):
        pending(m, report, "polynomial_miller_bit", bit_index=j)
        result, slope, kind = curve.add(u, u)
        line, vertical = line_factors(curve, u, u, result, slope, kind)
        numerator = ring_mul(curve, ring_mul(curve, numerator, numerator), line)
        put(m, report, "current_numerator", numerator)
        denominator = ring_mul(curve, ring_mul(curve, denominator, denominator), vertical)
        put(m, report, "current_denominator", denominator)
        u = result
        if not m.eq(m.read(digits, j), 0):
            result, slope, kind = curve.add(u, g)
            line, vertical = line_factors(curve, u, g, result, slope, kind)
            numerator = ring_mul(curve, numerator, line)
            put(m, report, "current_numerator", numerator)
            denominator = ring_mul(curve, denominator, vertical)
            put(m, report, "current_denominator", denominator)
            u = result
        m.tick("array_write", 4)
        m.append(report["steps"], m.record(bit_index=j, point=point_record(m, u),
                 numerator_lengths=[length(m, m.read(numerator, 0)), length(m, m.read(numerator, 1))],
                 denominator_lengths=[length(m, m.read(denominator, 0)), length(m, m.read(denominator, 1))]))
        done(m, report)
        j = m.sub(j, 1)
    need(m.eq(u, None), "polynomial Miller terminal point")
    npole, nlead, nnext = leading_pair(curve, numerator)
    dpole, dlead, dnext = leading_pair(curve, denominator)
    coefficient = f.sub(f.mul(nnext, f.inverse(nlead)), f.mul(dnext, f.inverse(dlead)))
    pole = m.sub(npole, dpole)
    need(m.eq(pole, curve.q), "polynomial Miller pole order")
    need(m.eq(coefficient, f.mul(m.rem(curve.q, curve.p), hg)), "independent Laurent coefficient")
    put(m, report, "pole_order", pole)
    put(m, report, "first_normalized_coefficient", coefficient)
    put(m, report, "completed", True)


def certify(base, curve, g, report):
    m, f = curve.m, curve.f
    m.phase = "certification"
    pending(m, report, "certification")
    need(base.prime_trial(m, curve.p), "p is not prime")
    need(base.prime_trial(m, curve.q), "q is not prime")
    need(m.lt(3, curve.p) and m.lt(3, curve.q), "small characteristic/order")
    need(not m.eq(curve.p, curve.q), "anomalous fixture")
    disc = f.add(f.mul(4, f.mul(f.square(curve.a), curve.a)), f.mul(27, f.square(curve.b)))
    need(not m.eq(disc, 0), "singular fixture")
    curve.check(g)
    need(m.eq(curve.scalar(curve.q, g), None), "qG is nonzero")
    delta = m.sub(curve.q, m.add(curve.p, 1))
    need(m.le(m.mul(delta, delta), m.mul(4, curve.p)), "q outside Hasse interval")
    need(m.lt(m.mul(16, curve.p), m.mul(curve.q, curve.q)), "q <= 4sqrt(p)")
    put(m, report, "certificate", "p,q prime; q!=p; smooth; G on curve; qG=O; Hasse and q>4sqrt(p)")
    done(m, report)


def enumerate_and_check(curve, g, report):
    m, f, q = curve.m, curve.f, curve.q
    m.phase = "binary_miller"
    hg = binary_h(curve, g, report["binary_checks"], "bootstrap_G")
    put(m, report, "hG", hg)
    m.phase = "enumeration"
    orbit = report["orbit"]
    pending(m, report, "allocate_fibre_arrays")
    raw, signed = [], []
    report["raw_fibres"], report["signed_fibres"] = raw, signed
    m.tick("trace_field", 2)
    a = 0
    while m.lt(a, curve.p):
        m.append(raw, 0); m.append(signed, 0)
        a = m.add(a, 1)
    done(m, report)
    point, h, i = None, 0, 0
    while m.lt(i, q):
        pending(m, report, "enumeration_point", index=i)
        curve.check(point)
        if m.eq(point, None):
            need(m.eq(i, 0) and m.eq(h, 0), "premature infinity or wrong hO")
        else:
            key, orientation = canonical(m, f, h)
            m.write(raw, h, m.add(m.read(raw, h), 1))
            m.write(signed, key, m.add(m.read(signed, key), 1))
        m.append(orbit, m.record(index=i, point=point_record(m, point), h=h))
        point, h, _ = curve.add_h(point, h, g, hg)
        i = m.add(i, 1)
        done(m, report)
    need(m.eq(point, None) and m.eq(h, 0), "orbit did not close")
    put(m, report, "enumeration_completed", True)
    m.phase = "fibre_checks"
    total_c, total_d, m2, s2, a = 0, 0, 0, 0, 0
    while m.lt(a, curve.p):
        c, d = m.read(raw, a), m.read(signed, a)
        total_c, total_d = m.add(total_c, c), m.add(total_d, d)
        m2, s2 = m.add(m2, m.mul(c, c)), m.add(s2, m.mul(d, d))
        need(m.eq(m.rem(d, 2), 0), "odd signed fibre")
        a = m.add(a, 1)
    qm1 = m.sub(q, 1)
    c0 = m.read(raw, 0)
    need(m.eq(total_c, qm1) and m.eq(total_d, qm1), "fibre total")
    need(m.eq(s2, m.sub(m.mul(2, m2), m.mul(c0, c0))), "signed moment identity")
    need(m.le(m.mul(2, qm1), s2) and m.le(s2, m.mul(6, qm1)), "proved fibre bound")
    i, chisum = 1, 0
    exponent = m.div(m.sub(curve.p, 1), 2)
    while m.lt(i, q):
        pending(m, report, "discriminant_and_oddness", index=i)
        row, opposite = m.read(orbit, i), m.read(orbit, m.sub(q, i))
        p, h = row["point"], row["h"]
        op = opposite["point"]
        need(m.eq(p["x"], op["x"]) and m.eq(f.add(p["y"], op["y"]), 0), "opposite coordinates")
        need(m.eq(opposite["h"], f.sub(0, h)), "odd h identity")
        h2 = f.square(h)
        delta = f.add(f.sub(f.sub(f.sub(f.square(h2), f.mul(6, f.mul(p["x"], h2))),
                          f.mul(3, f.square(p["x"]))), f.mul(4, curve.a)),
                      f.mul(8, f.mul(h, p["y"])))
        symbol = 0
        if not m.eq(delta, 0):
            powered = f.power(delta, exponent)
            if m.eq(powered, 1):
                symbol = 1
            else:
                need(m.eq(powered, m.sub(curve.p, 1)), "Euler character value")
                symbol = -1
        chisum = m.add(chisum, symbol)
        put(m, row, "residual_discriminant", delta)
        put(m, row, "discriminant_character", symbol)
        i = m.add(i, 1)
        done(m, report)
    need(m.eq(m2, m.add(m.mul(2, qm1), chisum)), "exact discriminant moment identity")
    put(m, report, "fibres", m.record(c0=c0, M2=m2, S2=s2,
        rho_numerator=s2, rho_denominator=m.mul(2, qm1), chi_sum=chisum, completed=True))
    m.phase = "binary_miller"
    checks = []
    for_const = (1, 2, 3, 4, 17)
    j = 0
    while m.lt(j, 5):
        m.append(checks, m.read(for_const, j)); j = m.add(j, 1)
    m.append(checks, m.sub(q, 2)); m.append(checks, m.sub(q, 1))
    m.append(checks, m.div(q, 2)); m.append(checks, m.div(m.add(q, 1), 2))
    j = 0
    while m.lt(j, length(m, checks)):
        index = m.read(checks, j)
        row = m.read(orbit, index)
        point = Point(row["point"]["x"], row["point"]["y"])
        actual = binary_h(curve, point, report["binary_checks"], "fixed_index_" + str(index))
        need(m.eq(actual, row["h"]), "sampled independent Miller h")
        j = m.add(j, 1)
    return hg


def orbit_point(m, orbit, i):
    row = m.read(orbit, i)
    p = row["point"]
    return (None if m.eq(p["infinity"], True) else Point(p["x"], p["y"])), row["h"]


def addition_checks(curve, report):
    m, f, q = curve.m, curve.f, curve.q
    m.phase = "addition_law_reference"
    pairs = report["addition_checks"]
    t = 0
    while m.lt(t, 70):
        if m.lt(t, 64):
            i, j = m.rem(t, q), m.rem(m.add(m.mul(t, t), 17), q)
        else:
            extra = ((0, 0), (0, 1), (1, 0), (1, m.sub(q, 1)), (1, 1), (m.sub(q, 1), m.sub(q, 1)))
            m.tick("array_write", 6)
            i, j = m.read(extra, m.sub(t, 64))
        pending(m, report, "addition_spot_check", i=i, j=j)
        p, hp = orbit_point(m, report["orbit"], i)
        r, hr = orbit_point(m, report["orbit"], j)
        result, slope, kind = curve.add(p, r)
        expected, he = orbit_point(m, report["orbit"], m.rem(m.add(i, j), q))
        need(curve.equal(result, expected), "spot group sum")
        if m.eq(kind, "identity_left"):
            actual = hr
        elif m.eq(kind, "identity_right"):
            actual = hp
        elif m.eq(kind, "vertical"):
            actual = f.add(hp, hr)
        else:
            actual = f.sub(f.add(hp, hr), slope)
        need(m.eq(actual, he), "spot addition defect")
        m.append(pairs, m.record(i=i, j=j, kind=kind, resulting_h=actual))
        done(m, report)
        t = m.add(t, 1)


def batch_inverse(curve, values):
    m, f = curve.m, curve.f
    n = length(m, values)
    if m.eq(n, 0):
        return []
    prefixes = []
    first = m.read(values, 0)
    need(not m.eq(first, 0), "zero batch denominator")
    m.append(prefixes, first)
    i = 1
    while m.lt(i, n):
        value = m.read(values, i)
        need(not m.eq(value, 0), "zero batch denominator")
        m.append(prefixes, f.mul(m.read(prefixes, m.sub(i, 1)), value))
        i = m.add(i, 1)
    inv = f.inverse(m.read(prefixes, m.sub(n, 1)))
    result = m.zeroes(n)
    i = m.sub(n, 1)
    while m.lt(0, i):
        m.write(result, i, f.mul(inv, m.read(prefixes, m.sub(i, 1))))
        inv = f.mul(inv, m.read(values, i))
        i = m.sub(i, 1)
    m.write(result, 0, inv)
    return result


class Buckets:
    """Explicit linear-probing directory; no free Python dict lookup oracle."""
    def __init__(self, m, maximum):
        self.m = m
        capacity = 1
        while m.lt(capacity, m.mul(2, maximum)):
            capacity = m.mul(2, capacity)
        self.mask = m.sub(capacity, 1)
        self.table = []
        i = 0
        while m.lt(i, capacity):
            m.append(self.table, None); i = m.add(i, 1)

    def get(self, key, create=False):
        m = self.m
        slot = m.band(m.mul(key, 2654435761), self.mask)
        while True:
            entry = m.read(self.table, slot)
            if m.eq(entry, None):
                if create:
                    bucket = []
                    m.write(self.table, slot, (key, bucket))
                    return bucket
                return None
            if m.eq(entry[0], key):
                return entry[1]
            slot = m.band(m.add(slot, 1), self.mask)


class Grid:
    """Candidate path has no orbit-table argument and never reads secret 17."""
    def __init__(self, curve, g, target, stride, size, seed, report):
        self.c, self.m, self.f = curve, curve.m, curve.f
        self.g, self.target, self.stride, self.size = g, target, stride, size
        self.r = report
        self.archives, self.offsets, self.states = [], [], []
        self.tables = []
        self.s = self.shift = None
        self.total_records = self.raw = self.false = self.genuine = self.recon = 0
        self.regular_pairs = self.exception_pairs = 0
        self.first = None
        self.seed = seed
        self.snapshot_frozen = False
        self.start_categories = {phase: dict(counts) for phase, counts in self.m.by_phase_kind.items()}
        self.start_inverses = {phase: tuple(counts) for phase, counts in self.f.inverse_by_phase.items()}

    def setup(self):
        m, f, c = self.m, self.f, self.c
        m.phase = "candidate_setup"
        pending(m, self.r, "candidate_setup")
        m.tick("bit_xor", 2)
        state = self.seed ^ c.p ^ c.q
        outputs = []
        i = 0
        while m.lt(i, 2):
            state = m.rem(m.add(m.mul(1664525, state), 1013904223), 4294967296)
            upper = m.shr(state, 16)
            m.tick("bit_xor")
            m.append(outputs, state ^ upper)
            i = m.add(i, 1)
        self.s = m.add(1, m.rem(m.read(outputs, 0), m.sub(c.q, 1)))
        self.shift = m.rem(m.read(outputs, 1), c.q)
        gp = c.scalar(self.s, self.g)
        qp, _, _ = c.add(self.target, c.scalar(self.shift, self.g))
        put(m, self.r, "randomization", m.record(s=self.s, shift=self.shift,
            Gprime=point_record(m, gp), Qprime=point_record(m, qp), iid=False))
        m.phase = "candidate_setup_miller"
        hgp = binary_h(c, gp, self.r["miller"], "Gprime")
        hqp = binary_h(c, qp, self.r["miller"], "Qprime")
        m.phase = "candidate_setup"
        dt, hdt = c.scalar_h(self.stride, gp, hgp)
        negdt, hnegdt = c.neg(dt), f.sub(0, hdt)
        side = 0
        while m.lt(side, 2):
            if m.eq(side, 0):
                start, hs, step, ht = None, 0, gp, hgp
            else:
                start, hs, step, ht = qp, hqp, negdt, hnegdt
            twice, htwice, _ = c.add_h(step, ht, step, ht)
            offsets = []
            m.append(offsets, (step, ht)); m.append(offsets, (twice, htwice))
            m.append(self.offsets, offsets)
            advance, ha = c.scalar_h(10, step, ht)
            centers = []
            j = 0
            while m.lt(j, 2):
                index = m.add(2, m.mul(5, j))
                delta, hd = c.scalar_h(index, step, ht)
                center, hc, _ = c.add_h(start, hs, delta, hd)
                m.append(centers, (center, hc, index))
                j = m.add(j, 1)
            m.append(self.states, {"centers": centers, "advance": advance, "ha": ha})
            m.append(self.tables, Buckets(m, self.size))
            side = m.add(side, 1)
        if m.eq(qp, None):
            self.verify_direct(0, "Qprime_infinity")
        m.phase = "candidate_setup"
        done(m, self.r)

    def actual_h(self, record):
        if self.m.eq(record["orientation"], 1):
            return record["key"]
        return self.f.sub(0, record["key"])

    def reference(self, center, hc, offset, ho, sign, generated_h):
        m, f = self.m, self.f
        old = m.phase
        m.phase = "reference_generation_validation"
        if m.eq(sign, -1):
            offset, ho = self.c.neg(offset), f.sub(0, ho)
        result, expected_h, kind = self.c.add_h(center, hc, offset, ho)
        need(m.eq(expected_h, generated_h), "candidate side h differs from affine reference")
        self.c.check(result)
        ref = point_record(m, result)
        m.phase = old
        return ref

    def make_record(self, side, index, archive, offset_index, sign, h, reference, cached=False, actual=None):
        m, f = self.m, self.f
        key, orientation = canonical(m, f, h)
        # Regular distinct-x sides are finite by the addition law. Reference
        # coordinates are evidence only, never candidate cache/dispatch inputs.
        infinity = m.eq(actual, None) if cached else False
        old_phase = m.phase
        m.phase = "reference_descriptor_validation"
        need(m.eq(infinity, reference["infinity"]), "candidate infinity dispatch mismatch")
        m.phase = old_phase
        record = m.record(id=self.total_records, side=side, index=index,
            archive=archive, offset_index=offset_index, sign=sign, key=key,
            orientation=orientation, h_evidence=h, reference=reference,
            is_infinity=infinity, cached=cached,
            cached_x=actual.x if cached and not infinity else None)
        self.total_records = m.add(self.total_records, 1)
        return record

    def reconstruct(self, record, audit=False):
        m, f = self.m, self.f
        need(not m.eq(record["is_infinity"], True), "infinity passed to finite reconstruction")
        if not audit and m.eq(record["cached"], True):
            return record["cached_x"]
        arc = m.read(self.archives, record["archive"])
        if m.eq(record["offset_index"], 0):
            x = arc.x
        else:
            offsets = m.read(self.offsets, record["side"])
            offset, ho = m.read(offsets, m.sub(record["offset_index"], 1))
            if m.eq(record["sign"], -1):
                ho = f.sub(0, ho)
            slope = f.sub(f.add(arc.h, ho), self.actual_h(record))
            x = f.sub(f.sub(f.square(slope), arc.x), offset.x)
        old_phase = m.phase
        m.phase = "reference_descriptor_validation"
        need(m.eq(x, record["reference"]["x"]), "one-square reconstructed x mismatch")
        m.phase = old_phase
        if not audit:
            new_count = m.add(self.recon, 1)
            m.tick("trace_field", 3)
            record["cached_x"], record["cached"], self.recon = x, True, new_count
        return x

    def verify_scalar(self, kp, reason, baby=None, giant=None, sign=None):
        m, c = self.m, self.c
        old = m.phase
        m.phase = "verification"
        scalar = m.rem(m.sub(m.mul(self.s, kp), self.shift), c.q)
        answer = c.scalar(scalar, self.g)
        valid = c.equal(answer, self.target)
        entry = m.record(kprime=kp, recovered_scalar=scalar, valid=valid, reason=reason,
                         baby=baby, giant=giant, sign=sign)
        m.append(self.r["verifications"], entry)
        if valid and m.eq(self.first, None):
            self.first = entry
            put(m, self.r, "first_success", entry)
        m.phase = old
        return valid

    def verify_direct(self, j, reason):
        if self.m.eq(self.first, None):
            kp = self.m.rem(self.m.mul(j, self.stride), self.c.q)
            need(self.verify_scalar(kp, reason), "direct infinity recovery failed")

    def inspect(self, record):
        m = self.m
        m.phase = "matching"
        if m.eq(record["is_infinity"], True):
            if m.eq(record["side"], 1):
                self.verify_direct(record["index"], "giant_infinity")
            else:
                need(m.eq(record["index"], 0), "unexpected nonzero baby infinity")
            put(m, record, "dispatched_before_bucket", True)
            return
        opposite = m.read(self.tables, m.sub(1, record["side"]))
        matches = opposite.get(record["key"])
        if not m.eq(matches, None):
            j = 0
            while m.lt(j, length(m, matches)):
                other = m.read(matches, j)
                pending(m, self.r, "raw_match", first=record["id"], second=other["id"])
                self.raw = m.add(self.raw, 1)
                m.phase = "reconstruction"
                x1, x2 = self.reconstruct(record), self.reconstruct(other)
                m.phase = "matching"
                same = m.eq(x1, x2)
                if same:
                    self.genuine = m.add(self.genuine, 1)
                    if m.eq(record["side"], 0):
                        baby, giant = record, other
                    else:
                        baby, giant = other, record
                    if m.eq(self.first, None):
                        if m.eq(record["key"], 0):
                            signs = (1, -1)
                        elif m.eq(self.actual_h(baby), self.actual_h(giant)):
                            signs = (1,)
                        else:
                            signs = (-1,)
                        si = 0
                        while m.lt(si, length(m, signs)):
                            sign = m.read(signs, si)
                            kp = m.rem(m.add(m.mul(giant["index"], self.stride),
                                            m.mul(sign, baby["index"])), self.c.q)
                            if self.verify_scalar(kp, "signed_x_match", baby["index"], giant["index"], sign):
                                break
                            si = m.add(si, 1)
                        need(not m.eq(self.first, None), "genuine point match did not recover target")
                else:
                    self.false = m.add(self.false, 1)
                m.append(self.r["matches"], m.record(first=record["id"], second=other["id"], exact_x_match=same))
                done(m, self.r)
                j = m.add(j, 1)
        own = m.read(self.tables, record["side"])
        m.append(own.get(record["key"], True), record)

    def block(self, side):
        m, f, c = self.m, self.f, self.c
        m.phase = "candidate_generation"
        state = m.read(self.states, side)
        block = {"side": side, "records": [], "completed": False, "pending": None}
        m.append(self.r["blocks"], block)
        m.tick("trace_field", 4)
        pending(m, self.r, "generation_block", side=side)
        slots = []
        put(m, block, "generated_slots", slots)
        j = 0
        while m.lt(j, 10):
            m.append(slots, None)
            j = m.add(j, 1)
        aids = []
        j = 0
        while m.lt(j, 2):
            center, hc, index = m.read(state["centers"], j)
            aid = length(m, self.archives)
            # Immutable TWO-field snapshot; never a reference to mutable centers.
            arc = Archive(None if m.eq(center, None) else center.x, hc)
            m.append(self.archives, arc)
            m.append(self.r["archives"], m.record(id=aid, x=arc.x, h=hc))
            m.append(aids, aid)
            ref = point_record(m, center)
            record = self.make_record(side, index, aid, 0, 1, hc, ref, True, center)
            m.write(slots, m.add(m.mul(5, j), 2), record)
            j = m.add(j, 1)
        offset_index = 1
        while m.le(offset_index, 2):
            offsets = m.read(self.offsets, side)
            offset, ho = m.read(offsets, m.sub(offset_index, 1))
            denominators, eligible = [], []
            j = 0
            while m.lt(j, 2):
                center, hc, index = m.read(state["centers"], j)
                if not m.eq(center, None) and not m.eq(center.x, offset.x):
                    m.append(denominators, f.sub(center.x, offset.x)); m.append(eligible, j)
                j = m.add(j, 1)
            inverses = batch_inverse(c, denominators)
            j, ei = 0, 0
            while m.lt(j, 2):
                center, hc, index = m.read(state["centers"], j)
                aid = m.read(aids, j)
                regular = not m.eq(center, None) and not m.eq(center.x, offset.x)
                if regular:
                    need(m.eq(m.read(eligible, ei), j), "batch center order")
                    inv = m.read(inverses, ei)
                    ei = m.add(ei, 1)
                    lp = f.mul(f.sub(center.y, offset.y), inv)
                    lm = f.mul(f.add(center.y, offset.y), inv)
                    hp, hm = f.sub(f.add(hc, ho), lp), f.sub(f.sub(hc, ho), lm)
                    self.regular_pairs = m.add(self.regular_pairs, 1)
                else:
                    self.exception_pairs = m.add(self.exception_pairs, 1)
                sign = -1
                while m.le(sign, 1):
                    out_index = m.add(index, m.mul(sign, offset_index))
                    if regular:
                        actual = None  # not consulted for uncached regular sides
                        hs = hp if m.eq(sign, 1) else hm
                        ref = self.reference(center, hc, offset, ho, sign, hs)
                        cached = False
                    else:
                        op, oh = offset, ho
                        if m.eq(sign, -1):
                            op, oh = c.neg(offset), f.sub(0, ho)
                        actual, hs, _ = c.add_h(center, hc, op, oh)
                        ref = self.reference(center, hc, offset, ho, sign, hs)
                        need(m.eq(ref["infinity"], m.eq(actual, None)), "exception infinity mismatch")
                        cached = True  # exceptional full operation already produced x
                    record = self.make_record(side, out_index, aid, offset_index, sign, hs, ref, cached, actual)
                    slot = m.add(m.add(m.mul(5, j), 2), m.mul(sign, offset_index))
                    m.write(slots, slot, record)
                    sign = m.add(sign, 2)
                j = m.add(j, 1)
            offset_index = m.add(offset_index, 1)
        # The frozen H019 ledger includes full center advancement even on the
        # terminal block. No f-way batching with future blocks is performed.
        denominators = []
        advance = state["advance"]
        j = 0
        while m.lt(j, 2):
            center, hc, index = m.read(state["centers"], j)
            if not m.eq(center, None) and not m.eq(advance, None) and not m.eq(center.x, advance.x):
                m.append(denominators, f.sub(advance.x, center.x))
            j = m.add(j, 1)
        inverses = batch_inverse(c, denominators)
        j, ei = 0, 0
        while m.lt(j, 2):
            center, hc, index = m.read(state["centers"], j)
            if not m.eq(center, None) and not m.eq(advance, None) and not m.eq(center.x, advance.x):
                slope = f.mul(f.sub(advance.y, center.y), m.read(inverses, ei))
                ei = m.add(ei, 1)
                x = f.sub(f.sub(f.square(slope), center.x), advance.x)
                y = f.sub(f.mul(slope, f.sub(center.x, x)), center.y)
                center, hc = Point(x, y), f.sub(f.add(hc, state["ha"]), slope)
            else:
                center, hc, _ = c.add_h(center, hc, advance, state["ha"])
            m.write(state["centers"], j, (center, hc, m.add(index, 10)))
            j = m.add(j, 1)
        j = 0
        while m.lt(j, 10):
            record = m.read(slots, j)
            m.append(block["records"], record)
            self.inspect(record)
            j = m.add(j, 1)
        m.phase = "candidate_generation"
        put(m, block, "completed", True)
        done(m, self.r)

    def run(self):
        m = self.m
        self.setup()
        count = 0
        while m.lt(count, self.size):
            self.block(0)
            self.block(1)
            count = m.add(count, 10)
        need(not m.eq(self.first, None), "full paired grid found no verified recovery")
        # Independent descriptor audit after candidate matching. It does NOT
        # populate candidate caches or charge these audit squares to R.
        m.phase = "reference_descriptor_validation"
        bi = 0
        while m.lt(bi, length(m, self.r["blocks"])):
            block = m.read(self.r["blocks"], bi)
            ri = 0
            while m.lt(ri, length(m, block["records"])):
                record = m.read(block["records"], ri)
                if not m.eq(record["is_infinity"], True):
                    if m.eq(record["cached"], True):
                        need(m.eq(record["cached_x"], record["reference"]["x"]), "cached x audit")
                    else:
                        self.reconstruct(record, audit=True)
                ri = m.add(ri, 1)
            bi = m.add(bi, 1)
        put(m, self.r, "completed", True)

    def snapshot(self):
        # Administrative snapshot of already paid counters. No unfinished work
        # is completed here; a pending marker makes the partial status explicit.
        if self.snapshot_frozen:
            return
        self.r["counters"] = {"records_created": self.total_records,
            "raw_record_matches": self.raw, "false_record_matches": self.false,
            "genuine_record_matches": self.genuine, "cached_side_reconstructions_R": self.recon,
            "regular_side_pairs": self.regular_pairs, "exceptional_side_pairs": self.exception_pairs}
        categories, symbolic = {}, {}
        for phase, counts in self.m.by_phase_kind.items():
            before = self.start_categories.get(phase, {})
            delta = {name: value - before.get(name, 0) for name, value in counts.items()
                     if value != before.get(name, 0)}
            if not delta:
                continue
            categories[phase] = delta
            inv = self.f.inverse_by_phase.get(phase, (0, 0, 0))
            old = self.start_inverses.get(phase, (0, 0, 0))
            ic, im, iss = (inv[j] - old[j] for j in range(3))
            mm = delta.get("field_mul", 0) - im
            ss = delta.get("field_square", 0) - iss
            aa = delta.get("field_add", 0) + delta.get("field_sub", 0)
            symbolic[phase] = {"M_excluding_inverse_expansion": mm, "S_excluding_inverse_expansion": ss,
                "A": aa, "I": ic, "optimistic_projection_M_numerator": 5 * mm + 4 * ss + 40 * ic,
                "optimistic_projection_denominator": 5}
        self.r["case_phase_event_categories"] = categories
        self.r["case_phase_symbolic_arithmetic"] = symbolic
        self.r["projection_scope"] = "S/M=4/5,I/M=8,A/M=0; nonarithmetic events retained separately; no baseline/full-work pass"
        self.snapshot_frozen = bool(self.r.get("completed", False))


def forced_checks(curve, g, hg, stride, report):
    m, f, c = curve.m, curve.f, curve
    m.phase = "forced_reference_cases"
    rows = report["forced_cases"]
    pending(m, report, "forced_cases")
    def dispatch_test(target, shift, giant_index, name):
        case = {"case": name, "verifications": [], "first_success": None,
                "matches": [], "pending": None}
        m.append(rows, case); m.tick("trace_field", 5)
        grid = Grid(c, g, target, stride, 2, 0, case)
        grid.s, grid.shift = 1, shift
        # Access would raise: proving the actual inspect path bypasses lookup.
        grid.tables = None
        record = m.record(id=0, side=1, index=giant_index, is_infinity=True)
        put(m, case, "record", record)
        grid.inspect(record)
        need(m.eq(record.get("dispatched_before_bucket"), True), "forced actual dispatch")
        need(not m.eq(grid.first, None), "forced actual dispatch recovery")
        put(m, case, "table_access_forbidden", True)
        m.phase = "forced_reference_cases"
    # Direct paths use separately constructed known inputs, not secret 17.
    shifted, _, _ = c.add(g, c.scalar(m.sub(c.q, 1), g))
    need(m.eq(shifted, None), "forced Qprime=O")
    recovered = m.rem(m.sub(0, m.sub(c.q, 1)), c.q)
    need(c.equal(c.scalar(recovered, g), g), "forced zero-target recovery")
    dispatch_test(g, m.sub(c.q, 1), 0, "Qprime_O")
    dg = c.scalar(stride, g)
    giant, _, _ = c.add(dg, c.neg(dg))
    need(m.eq(giant, None) and c.equal(c.scalar(stride, g), dg), "forced giant O")
    dispatch_test(dg, 0, 1, "giant_O")
    # Force both nonzero-h orientations through the actual matcher; diagnostic
    # orbit data chooses a fixture, never candidate advice in any grid run.
    oi = 1
    while m.lt(oi, c.q):
        rr = m.read(report["orbit"], oi)
        if not m.eq(rr["h"], 0):
            break
        oi = m.add(oi, 1)
    need(m.lt(oi, c.q), "no nonzero h for signed orientation test")
    bp = c.scalar(oi, g)
    bh = binary_h(c, bp, report["binary_checks"], "forced_orientation")
    sg = 1
    while m.le(sg, 2):
        sign = 1 if m.eq(sg, 1) else -1
        target = c.scalar(m.rem(m.add(stride, m.mul(sign, oi)), c.q), g)
        case = {"case": "signed_orientation", "sign": sign, "verifications": [],
                "first_success": None, "matches": [], "pending": None}
        m.append(rows, case); m.tick("trace_field", 6)
        grid = Grid(c, g, target, stride, 2, 0, case)
        grid.s, grid.shift = 1, 0
        m.append(grid.tables, Buckets(m, 2)); m.append(grid.tables, Buckets(m, 2))
        gp, gh = (bp, bh) if m.eq(sign, 1) else (c.neg(bp), f.sub(0, bh))
        br = grid.make_record(0, oi, 0, 0, 1, bh, point_record(m, bp), True, bp)
        gr = grid.make_record(1, 1, 0, 0, 1, gh, point_record(m, gp), True, gp)
        grid.inspect(br); grid.inspect(gr)
        need(not m.eq(grid.first, None), "forced signed matcher failure")
        need(m.eq(length(m, case["verifications"]), 1), "nonzero h must select single sign")
        need(m.eq(grid.first["sign"], sign), "forced recovered orientation")
        m.phase = "forced_reference_cases"
        sg = m.add(sg, 1)
    sign = -1
    while m.le(sign, 1):
        center, hc = (c.neg(g), f.sub(0, hg)) if m.eq(sign, -1) else (g, hg)
        side = -1
        while m.le(side, 1):
            offset, ho = (c.neg(g), f.sub(0, hg)) if m.eq(side, -1) else (g, hg)
            result, hs, kind = c.add_h(center, hc, offset, ho)
            if not m.eq(result, None):
                slope = f.sub(f.add(hc, ho), hs)
                x = f.sub(f.sub(f.square(slope), center.x), offset.x)
                need(m.eq(x, result.x), "forced tangent one-square reconstruction")
            else:
                need(m.eq(hs, 0), "forced vertical hO")
            m.append(rows, m.record(case="C_equals_plus_or_minus_J", center_sign=sign,
                offset_sign=side, kind=kind, output=point_record(m, result), h=hs))
            side = m.add(side, 2)
        sign = m.add(sign, 2)
    zero = None
    i = 1
    while m.lt(i, c.q):
        row = m.read(report["orbit"], i)
        if m.eq(row["h"], 0):
            zero = Point(row["point"]["x"], row["point"]["y"])
            break
        i = m.add(i, 1)
    if m.eq(zero, None):
        m.append(rows, m.record(case="nonidentity_zero_key", present=False))
    else:
        # Orbit table selects a diagnostic case only. Independently recompute
        # h at that point and its operands; this is never candidate advice.
        hz = binary_h(c, zero, report["binary_checks"], "forced_nonidentity_zero")
        need(m.eq(hz, 0), "zero-key independent coefficient")
        center, hc, trial = g, hg, 1
        while True:
            offset, _, _ = c.add(zero, c.neg(center))
            if not m.eq(offset, None) and not m.eq(offset.x, center.x):
                break
            trial = m.add(trial, 1)
            need(m.le(trial, 4), "forced zero-key regular decomposition unavailable")
            center, hc = c.scalar_h(trial, g, hg)
        ho = binary_h(c, offset, report["binary_checks"], "forced_zero_offset")
        slope = f.add(hc, ho)
        x = f.sub(f.sub(f.square(slope), center.x), offset.x)
        need(m.eq(x, zero.x), "zero-key reconstruction")
        key, orientation = canonical(m, f, hz)
        need(m.eq(key, 0), "zero canonical key")
        m.append(rows, m.record(case="nonidentity_zero_key", present=True,
            point=point_record(m, zero), index=i, canonical_key=key,
            orientation_irrelevant=True, reconstructed_x=x))
        # Force the negative equality so the zero-key path must reject its
        # first (+) scalar and then verify the second (-) scalar.
        target = c.scalar(m.rem(m.sub(stride, i), c.q), g)
        case = {"case": "zero_key_two_sign_matcher", "verifications": [],
                "first_success": None, "matches": [], "pending": None}
        m.append(rows, case); m.tick("trace_field", 5)
        grid = Grid(c, g, target, stride, 2, 0, case)
        grid.s, grid.shift = 1, 0
        m.append(grid.tables, Buckets(m, 2)); m.append(grid.tables, Buckets(m, 2))
        nz = c.neg(zero)
        br = grid.make_record(0, i, 0, 0, 1, 0, point_record(m, zero), True, zero)
        gr = grid.make_record(1, 1, 0, 0, 1, 0, point_record(m, nz), True, nz)
        grid.inspect(br); grid.inspect(gr)
        need(m.eq(length(m, case["verifications"]), 2), "zero key did not try both signs")
        need(not m.eq(grid.first, None) and m.eq(grid.first["sign"], -1), "zero negative recovery")
        m.phase = "forced_reference_cases"
    done(m, report)


def run_fixture(base, m, values, index, report, active_grids):
    p, a, b, q, gx, gy, stride, size = values
    curve, g = Curve(base, m, p, a, b, q), Point(gx, gy)
    certify(base, curve, g, report)
    hg = enumerate_and_check(curve, g, report)
    if m.lt(index, 2):
        m.phase = "polynomial_miller"
        polynomial_miller(curve, g, hg, report)
    addition_checks(curve, report)
    forced_checks(curve, g, hg, stride, report)
    m.phase = "candidate_reference_target_setup"
    # The sole occurrence of the reference exponent in target construction.
    # Grid receives only this point, never this exponent or the orbit table.
    target = curve.scalar(17, g)
    put(m, report, "reference_Q", point_record(m, target))
    seed_index = 0
    while m.lt(seed_index, 3):
        m.phase = "case_setup"
        seed = m.read(SEEDS, seed_index)
        case = {"seed": seed, "completed": False, "pending": None, "miller": [],
                "blocks": [], "archives": [], "matches": [], "verifications": [], "first_success": None}
        m.append(report["cases"], case)
        m.tick("trace_field", 10)
        grid = Grid(curve, g, target, stride, size, seed, case)
        active_grids.append(grid)  # instrumentation registry, not candidate data
        grid.run()
        grid.snapshot()
        m.phase = "finite_accounting"
        qm1, babies = m.sub(q, 1), m.sub(size, 1)
        fibres = report["fibres"]
        numerator = m.mul(m.mul(babies, size), m.sub(fibres["S2"], m.mul(2, qm1)))
        denominator = m.mul(q, qm1)
        need(m.le(numerator, m.mul(m.mul(4, m.mul(babies, size)), qm1)), "false expectation bound")
        put(m, case, "uniform_fullcap_false_expectation", m.record(numerator=numerator,
            denominator=denominator, NOT_a_fixed_seed_prediction=True))
        # Symbolic squaring credit only; all RAM and candidate setup are retained
        # separately in the phase ledger. No complete-work pass is inferred.
        put(m, case, "regular_generation_squares_saved", m.mul(2, grid.regular_pairs))
        put(m, case, "reconstruction_squares_paid", grid.recon)
        put(m, case, "net_squaring_projection_before_other_costs", m.sub(m.mul(2, grid.regular_pairs), grid.recon))
        seed_index = m.add(seed_index, 1)
    put(m, report, "completed", True)


def execute():
    start = time.monotonic()
    # Controlled import: H018 has only definitions at module scope and guards
    # its CLI. -B is required by the protocol to avoid bytecode artifacts.
    spec = importlib.util.spec_from_file_location("h028_h018_support", SUPPORT)
    base = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = base
    spec.loader.exec_module(base)
    base.EVENT_CAP, base.SECONDS_CAP = EVENT_CAP, SECONDS_CAP
    m = base.Meter()
    m.started = start  # include controlled import/provenance wall time
    report = {"protocol": "H028-provisional-key-v1", "status": "in_progress",
        "event_cap": EVENT_CAP, "seconds_cap": SECONDS_CAP,
        "ledger": "expanded bounded-word modular RAM; not bit/hardware work",
        "fixtures": [], "pending": None, "diagnostic_only": True,
        "no_full_solver_or_asymptotic_gain_claim": True,
        "administration_excluded_from_events_but_walltime_included": True}
    grids = []
    code = 0
    try:
        report["hashes"] = {"protocol_sha256": hashlib.sha256(PROTOCOL.read_bytes()).hexdigest(),
            "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "H018_support_sha256": hashlib.sha256(SUPPORT.read_bytes()).hexdigest()}
        m.check_time()
        index = 0
        while m.lt(index, 4):
            m.phase = "fixture_setup"
            values = m.read(FIXTURES, index)
            p, a, b, q, gx, gy, stride, size = values
            fixture = {"index": index, "p": p, "A": a, "B": b, "q": q,
                "G": [gx, gy], "D": stride, "side_size": size, "completed": False,
                "pending": None, "orbit": [], "binary_checks": [], "addition_checks": [],
                "forced_cases": [], "cases": [], "enumeration_completed": False}
            m.append(report["fixtures"], fixture)
            m.tick("trace_field", 16)
            pending(m, report, "fixture", index=index)
            run_fixture(base, m, values, index, fixture, grids)
            done(m, report)
            index = m.add(index, 1)
        report["status"] = "completed_finite_correctness_diagnostic"
    except base.Halt as exc:
        report["status"] = "inconclusive_cap"
        report["error"] = "Effective H028 guard reached: 10000000 events / 55 seconds"
        report["support_exception_text_not_effective_limits"] = str(exc)
        code = 2
    except (Failure, base.Invalid) as exc:
        report["status"], report["error"] = "correctness_failure", str(exc)
        code = 3
    except Exception as exc:
        report["status"], report["error"] = "implementation_error", type(exc).__name__ + ": " + str(exc)
        code = 4
    for grid in grids:  # administrative snapshots, no completion of algorithms
        grid.snapshot()
    report["events"], report["phase_events"] = m.total, m.by_phase
    report["event_categories"], report["phase_event_categories"] = m.by_kind, m.by_phase_kind
    report["cap_hit"] = m.cap_hit
    report["elapsed_before_json_seconds"] = time.monotonic() - start
    report["exit_code"] = code
    payload = json.dumps(report, indent=2, sort_keys=True)
    elapsed = time.monotonic() - start
    if elapsed >= SECONDS_CAP and code == 0:
        report["status"], report["cap_hit"] = "inconclusive_cap", "wall_time_during_reporting"
        report["error"] = "55-second internal guard crossed during administration"
        report["exit_code"], code = 2, 2
        payload = json.dumps(report, indent=2, sort_keys=True)
    sys.stdout.write(payload + "\n")
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute", action="store_true", help="requires separate root run approval")
    args = parser.parse_args()
    if not args.execute:
        parser.error("review-only: --execute requires separate approval")
    return execute()


if __name__ == "__main__":
    raise SystemExit(main())
