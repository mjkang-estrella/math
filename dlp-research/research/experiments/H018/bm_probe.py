#!/usr/bin/env python3
"""H018 review-only implementation; do not execute without root approval.

Frozen experiment: ../../hypotheses/H018-bm-probe-v1.md. No numerical result
was used to write this file. This is not an ECDLP solver or a generic engine.

RAM convention: each bounded-word arithmetic/modular operation, comparison,
bit operation, dynamic array access, and trace field costs one event. Register
assignment and fixed record-field access do not. Modular +,-,* are primitives;
pow, inverse, primality, scalar multiplication, and BM are expanded. Loop
index arithmetic and comparisons are charged. Instrumentation counter updates,
timer checks, Python object administration, protocol SHA-256, and JSON encoding
are administrative, not solver operations. Their wall time is included. This
is NOT a Python-bytecode, bit-complexity, H014-equivalent, or hardware ledger.

The literal implementation charges coefficient index/loop work and exposes
phase reservations/overruns. The BM audit below uses the aggregate iteration
bound, not the preflight's simplistic per-coefficient allowance. No claim that
every other worst-case phase fits its reservation is made. No run, import-based
check, compilation, or self-test is authorized by this file's existence. Main
requires an explicit execution acknowledgement.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path


EVENT_CAP = 1_000_000
SECONDS_CAP = 60.0
P = 8191
MAX_SAMPLES = 128
STOP_L = 64
MAX_ORDER_TESTS = 96
MAX_Q_PRIMES = 64
PROTOCOL_PATH = Path(__file__).resolve().parents[2] / "hypotheses/H018-bm-probe-v1.md"


class Halt(Exception):
    pass


class Invalid(Exception):
    pass


class Meter:
    """Counter/timer machinery itself does not recursively charge events."""

    def __init__(self):
        self.started = time.monotonic()
        self.total = 0
        self.phase = "setup"
        self.by_phase = {}
        self.by_kind = {}
        self.by_phase_kind = {}
        self.step_max = {}
        self.cap_hit = None

    def check_time(self):
        if time.monotonic() - self.started >= SECONDS_CAP:
            self.cap_hit = "wall_time"
            raise Halt("global 60-second wall cap")

    def tick(self, kind, count=1):
        self.check_time()
        if self.total + count > EVENT_CAP:
            self.cap_hit = "events"
            raise Halt("global 1,000,000-event cap")
        self.total += count
        self.by_phase[self.phase] = self.by_phase.get(self.phase, 0) + count
        self.by_kind[kind] = self.by_kind.get(kind, 0) + count
        bucket = self.by_phase_kind.setdefault(self.phase, {})
        bucket[kind] = bucket.get(kind, 0) + count

    def add(self, a, b):
        self.tick("integer_add")
        return a + b

    def sub(self, a, b):
        self.tick("integer_sub")
        return a - b

    def mul(self, a, b):
        self.tick("integer_mul")
        return a * b

    def div(self, a, b):
        self.tick("integer_div")
        return a // b

    def rem(self, a, b):
        self.tick("integer_rem")
        return a % b

    def eq(self, a, b):
        self.tick("comparison")
        return a == b

    def lt(self, a, b):
        self.tick("comparison")
        return a < b

    def le(self, a, b):
        self.tick("comparison")
        return a <= b

    def band(self, a, b):
        self.tick("bit_and")
        return a & b

    def shr(self, a, b):
        self.tick("bit_shift")
        return a >> b

    def read(self, a, i):
        self.tick("array_read")
        return a[i]

    def write(self, a, i, value):
        self.tick("array_write")
        a[i] = value

    def append(self, a, value):
        self.tick("array_write")
        a.append(value)

    def record(self, **fields):
        # The field schema is fixed; charge the materialized record fields.
        self.tick("trace_field", len(fields))
        return fields

    def zeroes(self, n):
        a = []
        i = 0
        while self.lt(i, n):
            self.append(a, 0)
            i = self.add(i, 1)
        return a

    def step_audit(self, name, start):
        cost = self.total - start
        self.step_max[name] = max(cost, self.step_max.get(name, 0))
        if cost > 64:
            raise Invalid("projective formula exceeded the 64-event step allowance")


class Field:
    def __init__(self, meter, modulus):
        self.m = meter
        self.p = modulus

    def add(self, a, b):
        self.m.tick("field_add")
        return (a + b) % self.p

    def sub(self, a, b):
        self.m.tick("field_sub")
        return (a - b) % self.p

    def mul(self, a, b):
        self.m.tick("field_mul")
        return (a * b) % self.p

    def square(self, a):
        self.m.tick("field_square")
        return (a * a) % self.p

    def power(self, a, exponent):
        # Right-to-left binary powering; no builtin pow and no hidden inverse.
        result = 1
        while not self.m.eq(exponent, 0):
            if not self.m.eq(self.m.band(exponent, 1), 0):
                result = self.mul(result, a)
            exponent = self.m.shr(exponent, 1)
            if not self.m.eq(exponent, 0):
                a = self.square(a)
        return result

    def inverse(self, a):
        if self.m.eq(a, 0):
            raise Invalid("attempted inversion of zero")
        return self.power(a, self.m.sub(self.p, 2))


@dataclass(frozen=True)
class Point:
    x: int
    y: int
    z: int


O = Point(1, 1, 0)


class Curve:
    """Jacobian x=X/Z^2, y=Y/Z^3; general-a formulas with a=1.

    Primary formula source:
    https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html
    dbl-2007-bl and add-2007-bl. No a=0 or a=-3 specialization.
    Fixed Point attribute access is free register access under the stated RAM
    convention. Every modular arithmetic operation and exception comparison is
    charged. Ordinary doubling uses <=30 events; general addition <=40. An
    equal-point add includes its initial comparison arithmetic AND doubling;
    step_audit checks that entire branch against 64. The inverse-point branch
    returns O; Y=0 doubling returns O, even during unsuccessful fixture tests.
    """

    def __init__(self, meter, b):
        self.m = meter
        self.f = Field(meter, P)
        self.b = b

    def double(self, point):
        start = self.m.total
        result = self._double(point)
        self.m.step_audit("double", start)
        return result

    def _double(self, point):
        m, f = self.m, self.f
        if m.eq(point.z, 0) or m.eq(point.y, 0):
            return O
        xx = f.square(point.x)
        yy = f.square(point.y)
        yyyy = f.square(yy)
        zz = f.square(point.z)
        s = f.mul(2, f.sub(f.sub(f.square(f.add(point.x, yy)), xx), yyyy))
        # a=1: multiplying Z^4 by a is literally unnecessary.
        slope = f.add(f.mul(3, xx), f.square(zz))
        x3 = f.sub(f.square(slope), f.mul(2, s))
        y3 = f.sub(f.mul(slope, f.sub(s, x3)), f.mul(8, yyyy))
        z3 = f.sub(f.sub(f.square(f.add(point.y, point.z)), yy), zz)
        return Point(x3, y3, z3)

    def add(self, left, right):
        start = self.m.total
        result = self._add(left, right)
        self.m.step_audit("add_including_exceptions", start)
        return result

    def _add(self, left, right):
        m, f = self.m, self.f
        if m.eq(left.z, 0):
            return right
        if m.eq(right.z, 0):
            return left
        z1z1 = f.square(left.z)
        z2z2 = f.square(right.z)
        u1 = f.mul(left.x, z2z2)
        u2 = f.mul(right.x, z1z1)
        s1 = f.mul(f.mul(left.y, right.z), z2z2)
        s2 = f.mul(f.mul(right.y, left.z), z1z1)
        if m.eq(u1, u2):
            if m.eq(s1, s2):
                return self._double(left)
            return O
        h = f.sub(u2, u1)
        ii = f.square(f.mul(2, h))
        j = f.mul(h, ii)
        r = f.mul(2, f.sub(s2, s1))
        v = f.mul(u1, ii)
        x3 = f.sub(f.sub(f.square(r), j), f.mul(2, v))
        y3 = f.sub(f.mul(r, f.sub(v, x3)), f.mul(2, f.mul(s1, j)))
        z3 = f.mul(f.sub(f.sub(f.square(f.add(left.z, right.z)), z1z1), z2z2), h)
        return Point(x3, y3, z3)

    def scalar(self, n, point):
        m = self.m
        start = m.total
        if m.lt(n, 0) or not m.lt(n, 16384):
            raise Invalid("scalar outside frozen 14-bit implementation")
        if m.eq(n, 0):
            return O
        mask = 8192
        while m.lt(n, mask):
            mask = m.shr(mask, 1)
        result = point  # leading 1 bit, no unnecessary initial doubling of O
        mask = m.shr(mask, 1)
        while not m.eq(mask, 0):
            result = self.double(result)
            if not m.eq(m.band(n, mask), 0):
                result = self.add(result, point)
            mask = m.shr(mask, 1)
        cost = m.total - start  # instrumentation bookkeeping
        m.step_max["scalar"] = max(cost, m.step_max.get("scalar", 0))
        if cost > 1840:
            raise Invalid("scalar exceeded preflight allowance")
        return result

    def affine(self, point):
        if self.m.eq(point.z, 0):
            raise Invalid("unexpected infinity in sampled orbit")
        iz = self.f.inverse(point.z)
        iz2 = self.f.square(iz)
        return Point(self.f.mul(point.x, iz2), self.f.mul(point.y, self.f.mul(iz2, iz)), 1)

    def check_affine(self, point):
        f, m = self.f, self.m
        rhs = f.add(f.add(f.mul(f.square(point.x), point.x), point.x), self.b)
        if not m.eq(f.square(point.y), rhs) or m.eq(point.y, 0):
            raise Invalid("affine curve/nonzero-y check failed")


def prime_trial(m, n):
    if m.lt(n, 2):
        return False
    if m.eq(n, 2):
        return True
    if m.eq(m.rem(n, 2), 0):
        return False
    divisor = 3
    while m.le(m.mul(divisor, divisor), n):
        if m.eq(m.rem(n, divisor), 0):
            return False
        divisor = m.add(divisor, 2)
    return True


def distinct_prime_factors(m, n):
    factors = []
    divisor = 2
    while m.le(m.mul(divisor, divisor), n):
        if m.eq(m.rem(n, divisor), 0):
            m.append(factors, divisor)
            while m.eq(m.rem(n, divisor), 0):
                n = m.div(n, divisor)
        divisor = m.add(divisor, 1)
    if m.lt(1, n):
        m.append(factors, n)
    return factors


def select_fixture(m, report):
    m.phase = "selection_setup"
    if not prime_trial(m, P):
        raise Invalid("frozen p is not prime")
    q_primes = []
    q = 8011
    while m.le(q, 8373) and m.lt(len(q_primes), MAX_Q_PRIMES):
        # Exclude anomalous q=p BEFORE primality/list admission/order tests.
        if not m.eq(q, P) and prime_trial(m, q):
            m.append(q_primes, q)
        q = m.add(q, 2)
    report["q_candidates"] = q_primes
    report["selection_attempts"] = attempts = []
    order_tests = 0
    b = 1
    while m.le(b, 4):
        curve = Curve(m, b)
        f = curve.f
        if m.eq(f.add(4, f.mul(27, f.square(b))), 0):
            m.append(attempts, m.record(b=b, outcome="singular"))
            b = m.add(b, 1)
            continue
        # Frozen paper-derived prefilter: (-1,0) is rational 2-torsion when
        # (-1)^3+(-1)+b=0, impossible in a full odd-prime-order group.
        minus_one = f.sub(0, 1)
        at_minus_one = f.add(f.add(f.mul(f.square(minus_one), minus_one), minus_one), b)
        if m.eq(at_minus_one, 0):
            m.append(attempts, m.record(b=b, outcome="rational_two_torsion_at_minus_one"))
            b = m.add(b, 1)
            continue
        g = None
        x = 0
        while m.le(x, 15):
            h = f.add(f.add(f.mul(f.square(x), x), x), b)
            y = h
            j = 0
            while m.lt(j, 11):
                y = f.square(y)
                j = m.add(j, 1)
            if m.eq(f.square(y), h) and not m.eq(y, 0):
                other_y = m.sub(P, y)
                if m.lt(other_y, y):
                    y = other_y
                g = Point(x, y, 1)
                curve.check_affine(g)
                break
            x = m.add(x, 1)
        if m.eq(g, None):
            m.append(attempts, m.record(b=b, outcome="no_point_in_bounded_search"))
            b = m.add(b, 1)
            continue
        attempt = m.record(b=b, gx=g.x, gy=g.y, q_tests=[])
        m.append(attempts, attempt)
        qi = 0
        while m.lt(qi, len(q_primes)):
            if not m.lt(order_tests, MAX_ORDER_TESTS):
                raise Halt("fixture not found: global 96 order tests exhausted")
            q = m.read(q_primes, qi)
            m.phase = "order_certification"
            multiple = curve.scalar(q, g)
            is_zero = m.eq(multiple.z, 0)
            m.append(attempt["q_tests"], m.record(q=q, multiple_x=multiple.x,
                     multiple_y=multiple.y, multiple_z=multiple.z, is_zero=is_zero))
            order_tests = m.add(order_tests, 1)
            m.phase = "selection_setup"
            if is_zero:
                if not m.lt(8373, m.mul(2, q)):
                    raise Invalid("Hasse certificate condition failed")
                report["fixture"] = m.record(p=P, a=1, b=b, q=q, gx=g.x,
                    gy=g.y, order_tests=order_tests, hasse_lower=8011,
                    hasse_upper=8373, certificate="q prime; G != O; [q]G=O; 2q>8373")
                return curve, g, q
            qi = m.add(qi, 1)
        b = m.add(b, 1)
    raise Halt("fixture not found: four curves exhausted")


def primitive_element(m, q, report):
    m.phase = "selection_setup"
    q_minus_one = m.sub(q, 1)
    factors = distinct_prime_factors(m, q_minus_one)
    # Factorization is exact trial division; independently recheck its output
    # primes and full coverage instead of silently trusting a partial factor list.
    remaining = q_minus_one
    fi = 0
    while m.lt(fi, len(factors)):
        ell = m.read(factors, fi)
        if not prime_trial(m, ell):
            raise Invalid("factor certification failed")
        while m.eq(m.rem(remaining, ell), 0):
            remaining = m.div(remaining, ell)
        fi = m.add(fi, 1)
    if not m.eq(remaining, 1):
        raise Invalid("incomplete factorization")
    report["q_minus_one_distinct_prime_factors"] = factors
    m.phase = "primitive_w"
    f = Field(m, q)
    attempts = []
    report["primitive_attempts"] = attempts
    w = 2
    while m.le(w, 33):
        residues = []
        valid = True
        fi = 0
        while m.lt(fi, len(factors)):
            ell = m.read(factors, fi)
            exponent = m.div(q_minus_one, ell)
            residue = f.power(w, exponent)
            m.append(residues, m.record(ell=ell, exponent=exponent, residue=residue))
            if m.eq(residue, 1):
                valid = False
                break
            fi = m.add(fi, 1)
        m.append(attempts, m.record(w=w, passed=valid, tests=residues))
        if valid:
            report["primitive_w"] = w
            m.tick("trace_field")
            return w
        w = m.add(w, 1)
    raise Halt("no primitive w among 2,...,33")


class BM:
    """Standard connection convention sum_{j=0}^L C[j] s[n-j]=0.

    C and B have fixed capacity; Bdeg tracks the previous polynomial's valid
    prefix. Copy C only when 2L<=n and discrepancy !=0. Every coefficient
    read/write, index calculation, loop comparison, inverse, and copy is paid.
    A cap during an update leaves committed trace/prefix length unchanged in
    the certificate status: only entries in trace are completed updates.

    Static four-feature BM audit, for independent review (not measured):
    Before index n, L+Bdeg<=n, hence discrepancy plus update coefficient
    iterations <=n+1; sum for 128 inputs <=8256 per stream. A discrepancy
    iteration costs 7 events, an update iteration 9, including index checks.
    Bound both by 9: 4*8256*9=297216. Inverse+ratio <=101 per nonzero
    discrepancy: 51712. On degree changes old L visits distinct values in
    0..63; copying costs <=4*(4*2080+64)=33536. Other feed work <=27 events
    per sample: 13824. Both coefficient buffers and stream initialization cost
    <=3137 across four streams. Core sum <=399425; the first outer sample-loop
    comparison is also charged to this phase, giving <=399426 against400000.
    This relies on actual BM recurrence LENGTH, not degree(C), and includes a
    terminal update at index127 with an index128 write. It excludes neither
    trailing-zero copies nor failed/zero-discrepancy checks. It is deliberately
    a very tight paper bound and must be checked when changing this code.
    """

    def __init__(self, m, q, limit, capacity, name):
        self.m = m
        self.f = Field(m, q)
        self.limit = limit
        self.capacity = capacity
        self.name = name
        self.c = m.zeroes(m.add(capacity, 1))
        self.bpoly = m.zeroes(m.add(capacity, 1))
        m.write(self.c, 0, 1)
        m.write(self.bpoly, 0, 1)
        self.bdeg = 0
        self.last_discrepancy = 1
        self.shift = 1
        self.L = 0
        self.n = 0
        self.prefix = []
        self.trace = []
        self.stopped = False
        self.completed_L = 0
        self.completed_n = 0
        self.update_in_progress = False

    def feed(self, value):
        m, f = self.m, self.f
        if not m.lt(self.n, self.capacity) or m.eq(self.stopped, True):
            raise Invalid("BM input exceeds frozen stream")
        self.update_in_progress = True
        n, before_L = self.n, self.L
        before_shift, previous_discrepancy = self.shift, self.last_discrepancy
        m.append(self.prefix, value)
        discrepancy = value
        j = 1
        while m.le(j, self.L):
            term = f.mul(m.read(self.c, j), m.read(self.prefix, m.sub(n, j)))
            discrepancy = f.add(discrepancy, term)
            j = m.add(j, 1)
        ratio = 0
        changed = False
        if m.eq(discrepancy, 0):
            self.shift = m.add(self.shift, 1)
        else:
            ratio = f.mul(discrepancy, f.inverse(self.last_discrepancy))
            changed = m.le(m.mul(2, self.L), n)
            old_c = None
            if changed:
                old_c = []
                j = 0
                while m.le(j, self.L):
                    m.append(old_c, m.read(self.c, j))
                    j = m.add(j, 1)
            j = 0
            while m.le(j, self.bdeg):
                index = m.add(j, self.shift)
                if not m.le(index, self.capacity):
                    raise Invalid("BM coefficient index overflow")
                corrected = f.sub(m.read(self.c, index), f.mul(ratio, m.read(self.bpoly, j)))
                m.write(self.c, index, corrected)
                j = m.add(j, 1)
            if changed:
                self.bpoly = old_c
                self.bdeg = self.L
                self.L = m.sub(m.add(n, 1), self.L)
                self.last_discrepancy = discrepancy
                self.shift = 1
            else:
                self.shift = m.add(self.shift, 1)
        if not m.eq(m.read(self.c, 0), 1):
            raise Invalid("BM constant coefficient invariant failed")
        next_n = m.add(n, 1)
        if not m.le(self.L, next_n):
            raise Invalid("BM degree exceeds prefix length")
        stopped = not m.lt(self.L, self.limit)
        entry = m.record(index=n, value=value, discrepancy=discrepancy,
            previous_discrepancy=previous_discrepancy, ratio=ratio,
            before_L=before_L, after_L=self.L, before_shift=before_shift,
            after_shift=self.shift, degree_update=changed, reached_limit=stopped)
        m.append(self.trace, entry)
        # Commit only after the charged trace append completed successfully.
        self.n = next_n
        self.completed_n = next_n
        self.completed_L = self.L
        self.stopped = stopped
        self.update_in_progress = False

    def verify_recurrence(self):
        m, f = self.m, self.f
        n = self.L
        while m.lt(n, self.n):
            discrepancy = 0
            j = 0
            while m.le(j, self.L):
                discrepancy = f.add(discrepancy, f.mul(m.read(self.c, j),
                    m.read(self.prefix, m.sub(n, j))))
                j = m.add(j, 1)
            if not m.eq(discrepancy, 0):
                raise Invalid("planted-control recurrence validation failed")
            n = m.add(n, 1)

    def administrative_snapshot(self):
        # References to already paid records; no numerical transformation.
        return {"name": self.name, "threshold": self.limit,
            "completed_prefix_length": self.completed_n,
            "completed_L": self.completed_L,
            "threshold_reached": self.stopped,
            "update_in_progress": self.update_in_progress,
            "prefix_including_any_uncommitted_last_input": self.prefix,
            "completed_update_trace": self.trace,
            "current_connection_buffer_may_be_partial_on_cap": self.c,
            "current_previous_polynomial": self.bpoly,
            "current_previous_degree": self.bdeg,
            "current_shift": self.shift,
            "current_previous_discrepancy": self.last_discrepancy}


def controls(m, q, w, report, states):
    m.phase = "controls"
    f = Field(m, q)
    planted = BM(m, q, 64, 16, "planted_three_powers")
    m.append(states, planted)
    u, v = 1, 1
    w2 = f.square(w)
    i = 0
    while m.lt(i, 16):
        planted.feed(f.add(f.add(1, f.mul(2, u)), f.mul(3, v)))
        u = f.mul(u, w)
        v = f.mul(v, w2)
        i = m.add(i, 1)
    if not m.eq(planted.L, 3):
        raise Invalid("planted control did not recover complexity 3")
    planted.verify_recurrence()
    report["planted_control_validated"] = True
    m.tick("trace_field")
    pseudo = BM(m, q, 32, 64, "fixed_LCG_not_an_iid_null")
    m.append(states, pseudo)
    state = 18018
    i = 0
    while m.lt(i, 64) and m.eq(pseudo.stopped, False):
        state = m.rem(m.add(m.mul(1664525, state), 1013904223), 4294967296)
        pseudo.feed(m.rem(state, q))
        i = m.add(i, 1)
    report["controls_completed"] = True
    m.tick("trace_field")


def centered(m, value):
    if m.lt(4095, value):
        return m.sub(value, P)
    return value


def feature_value(m, curve, affine, q, feature):
    # Dispatch comparisons are charged; no computation for stopped features.
    if m.eq(feature, 0):
        return m.rem(centered(m, affine.x), q)
    if m.eq(feature, 1):
        return m.rem(centered(m, affine.y), q)
    if m.eq(feature, 2):
        x, y = centered(m, affine.x), centered(m, affine.y)
        numerator = m.sub(m.sub(m.sub(m.mul(y, y), m.mul(m.mul(x, x), x)), x), curve.b)
        if not m.eq(m.rem(numerator, P), 0):
            raise Invalid("kappa numerator not divisible by p")
        return m.rem(m.div(numerator, P), q)
    # The frozen fourth and final feature is center_p(-x/y) mod q.
    if not m.eq(feature, 3):
        raise Invalid("unknown feature")
    parameter = curve.f.sub(0, curve.f.mul(affine.x, curve.f.inverse(affine.y)))
    return m.rem(centered(m, parameter), q)


def run_features(m, curve, g, q, w, report, states):
    m.phase = "bm"
    names = ("centered_x", "centered_y", "kappa", "centered_formal_parameter")
    fi = 0
    while m.lt(fi, 4):
        name = m.read(names, fi)
        m.append(states, BM(m, q, STOP_L, MAX_SAMPLES, name))
        fi = m.add(fi, 1)
    samples = []
    report["shared_affine_samples"] = samples
    point = g
    i = 0
    while m.lt(i, MAX_SAMPLES):
        m.phase = "features"
        affine = curve.affine(point)
        curve.check_affine(affine)
        m.append(samples, m.record(index=i, x=affine.x, y=affine.y))
        active = 0
        fi = 0
        while m.lt(fi, 4):
            state = m.read(states, fi)
            m.tick("comparison")
            if not state.stopped:
                value = feature_value(m, curve, affine, q, fi)
                m.phase = "bm"
                state.feed(value)
                m.phase = "features"
            m.tick("comparison")
            if not state.stopped:
                active = m.add(active, 1)
            fi = m.add(fi, 1)
        i = m.add(i, 1)
        if m.eq(active, 0) or not m.lt(i, MAX_SAMPLES):
            break
        m.phase = "orbit_scalar"
        point = curve.scalar(w, affine)
    report["feature_sampling_completed"] = True
    m.tick("trace_field")


RESERVATIONS = {
    "selection_setup": 35000,
    "order_certification": 176640,
    "primitive_w": 25000,
    "orbit_scalar": 233680,
    "features": 35000,
    "bm": 400000,
    "controls": 35000,
    "setup": 20000,
}


def execute():
    m = Meter()
    report = {
        "protocol": "H018-bm-probe-v1",
        "implementation_status": "review-only implementation; results require separate approval",
        "ledger_unit": "bounded-word modular RAM events; not H014 or hardware units",
        "event_cap": EVENT_CAP,
        "seconds_cap": SECONDS_CAP,
        "planted_control_validated": False,
        "controls_completed": False,
        "feature_sampling_completed": False,
        "status": "in_progress",
        "provenance_and_encoding_excluded_from_event_count": True,
        "administrative_wall_time_included": True,
        "paper_phase_reservations_not_proven_upper_bounds": RESERVATIONS,
    }
    control_states = []
    feature_states = []
    try:
        # File reading/hash are provenance, never fixture/advice generation.
        raw_protocol = PROTOCOL_PATH.read_bytes()
        report["protocol_sha256"] = hashlib.sha256(raw_protocol).hexdigest()
        report["protocol_bytes"] = len(raw_protocol)
        report["implementation_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        m.check_time()
        curve, g, q = select_fixture(m, report)
        w = primitive_element(m, q, report)
        controls(m, q, w, report, control_states)
        run_features(m, curve, g, q, w, report, feature_states)
        report["status"] = "completed_finite_diagnostic_only"
    except Halt as exc:
        report["status"] = "inconclusive"
        report["halt_reason"] = str(exc)
    except Invalid as exc:
        report["status"] = "invalid_or_failed_implementation_preflight"
        report["halt_reason"] = str(exc)
    except Exception as exc:
        # Preserve prefixes on unexpected implementation failures; never label
        # these as successful mathematical exclusions.
        report["status"] = "implementation_error"
        report["halt_reason"] = type(exc).__name__ + ": " + str(exc)
    # Administrative serialization references already metered data. No further
    # algebra or completion of an interrupted BM update happens in this path.
    report["controls"] = [state.administrative_snapshot() for state in control_states]
    report["features"] = [state.administrative_snapshot() for state in feature_states]
    report["events"] = m.total
    report["phase_events"] = m.by_phase
    report["event_categories"] = m.by_kind
    report["phase_event_categories"] = m.by_phase_kind
    report["observed_max_projective_step_events"] = m.step_max
    report["cap_hit"] = m.cap_hit
    report["phase_reservation_overruns"] = {
        phase: count - RESERVATIONS.get(phase, 0)
        for phase, count in m.by_phase.items()
        if count > RESERVATIONS.get(phase, 0)
    }
    report["elapsed_before_json_encoding_seconds"] = time.monotonic() - m.started
    payload = json.dumps(report, indent=2, sort_keys=True)
    elapsed = time.monotonic() - m.started
    # If administration itself crosses the cap, do not emit a completed status.
    if elapsed >= SECONDS_CAP and report["cap_hit"] is None:
        report["status"] = "inconclusive"
        report["cap_hit"] = "wall_time_during_reporting"
        report["halt_reason"] = "60-second budget exceeded during administrative reporting"
        report["elapsed_after_initial_json_encoding_seconds"] = elapsed
        payload = json.dumps(report, indent=2, sort_keys=True)
    sys.stdout.write(payload + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--approved-execution", action="store_true",
                        help="acknowledge separate root approval; this flag does not grant it")
    args = parser.parse_args()
    if not args.approved_execution:
        parser.error("review-only: numerical execution requires separate root approval")
    execute()


if __name__ == "__main__":
    main()
