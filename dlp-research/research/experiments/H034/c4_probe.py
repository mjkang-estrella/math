#!/usr/bin/env python3
"""Standalone H034 protocol-v2 finite synthetic correctness/ledger diagnostic.

SOURCE ONLY until independent static review and root's separate one-run admission.
No imports of experiment modules; importing this file does no numerical work.
Only --execute --output PATH invokes the fixed diagnostic. No tunable fixtures,
seeds, target ranges, caps, retries, solver policy, or arithmetic configurations.

Modular-RAM primitives (one event each): integer +,-,*,//,%, comparison,
bit &, xor, shift; modular Fp/Fq A,M,S; one record-word read/write; array-slot
reservation/initialization/release; allocation header; length; chain probe;
RNG draw/rejection; descriptor decode; verification boundary. Field reductions
are part of the declared modular primitive. Conditional tests use comparison
or branch events. Loop tests and index increments are explicit. Fixed-schema
register assignment and instrumentation/report bookkeeping are administrative.
Dynamic solver storage is Arena only; no Python dict/hash lookup solves a DLP.
Immutable point tuples are fixed-register records: coordinate reads are paid,
array copies pay their full declared word width. Ordinary group arithmetic,
primality, inverses, RNG and scalar multiplication are expanded. Completed
symbolic I is a projection of raw M/S, NEVER extra raw events. Bit widths and
packed capacities are descriptive models, not binary-tape or CPU-cycle bounds.
Python storage observations exclude retained reports and are approximate.

The full-range harness secret never enters a solver, root array, reference
checker, or lookup table. Reference validation only returns pass/fail; its
immutable point inputs never update solver state. The baseline exponent stays
1/2; this named test can falsify correctness/accounting, not prove improvement.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import platform
import signal
import sys
import time

HERE = Path(__file__).resolve().parent
FIXTURES = ((59, 28, 27, 73, 34, 35), (101, 2, 31, 103, 0, 43),
            (251, 1, 4, 271, 0, 2), (8191, 1, 5, 8053, 0, 789))
SEEDS = (7, 19)
EXPECTED = ((3, 18, 13, 26, 16, 13, 7), (3, 18, 16, 32, 16, 15, 8),
            (3, 18, 25, 50, 32, 24, 12), (7, 98, 135, 270, 128, 127, 64))
CONFIGS = (((2, 1), (1, 2)), ((2, 1), (1, 2)),
           ((4, 1), (2, 2)), ((8, 1), (4, 3)))
TAGS = {'target': 0x54415247, 'labels': 0x4C414245,
        'hash': 0x48415348, 'fallback': 0x46414C4C}
EVENT_CAP, SECONDS_CAP = 1_000_000, 55.0


class Halt(Exception):
    """Resource censorship, never algorithmic failure/fallback."""


class Invalid(Exception):
    """Diagnostic falsifier or invalid public setup."""


class Meter:
    def __init__(self, report):
        self.report = report
        self.started = time.monotonic()
        self.total = 0
        self.phase = 'administrative/preflight'
        self.kinds, self.phases, self.inverses = {}, {}, {}
        self.components = []
        self.guard = None
        self.live = []  # Instrumentation registry, never read as solver advice.
        self.python_peak = {}

    def tick(self, kind, count=1):
        if time.monotonic() - self.started >= SECONDS_CAP:
            self.guard = 'internal_55s'
            raise Halt('aggregate internal 55-second work guard')
        if self.total + count > EVENT_CAP:
            self.guard = 'aggregate_events'
            raise Halt('aggregate 1,000,000 modular-RAM event cap')
        self.total += count
        self.kinds[kind] = self.kinds.get(kind, 0) + count
        row = self.phases.setdefault(self.phase, {})
        row[kind] = row.get(kind, 0) + count

    def add(self, a, b):
        self.tick('integer_add')
        return a + b

    def sub(self, a, b):
        self.tick('integer_sub')
        return a - b

    def mul(self, a, b):
        self.tick('integer_mul')
        return a * b

    def div(self, a, b):
        self.tick('integer_div')
        return a // b

    def rem(self, a, b):
        self.tick('integer_rem')
        return a % b

    def eq(self, a, b):
        self.tick('comparison')
        return a == b

    def lt(self, a, b):
        self.tick('comparison')
        return a < b

    def le(self, a, b):
        self.tick('comparison')
        return a <= b

    def band(self, a, b):
        self.tick('bit_and')
        return a & b

    def xor(self, a, b):
        self.tick('bit_xor')
        return a ^ b

    def shr(self, a, b):
        self.tick('bit_shift')
        return a >> b

    def maximum(self, a, b): return b if self.lt(a, b) else a

    def indices(self, n):
        i = 0
        while self.lt(i, n):
            yield i
            i = self.add(i, 1)

    def record(self, row, index):
        self.tick('field_record_read')
        return row[index]

    @contextmanager
    def scope(self, name):
        old = self.phase
        self.phase = name
        try:
            yield
        finally:
            self.phase = old

    def pending(self, operation, **fields):
        self.report['pending'] = {'phase': self.phase, 'operation': operation, **fields}

    def sample_storage(self):
        # Administrative observation; no solver access or pruning decision.
        seen = set()
        def visit(x):
            ident = id(x)
            if ident in seen:
                return 0
            seen.add(ident)
            size = sys.getsizeof(x)
            if isinstance(x, (list, tuple)):
                size += sum(visit(v) for v in x)
            return size
        payload = sum(visit(a.data) for a in self.live if not a.released)
        total = payload + sum(sys.getsizeof(a) for a in self.live if not a.released)
        old = self.python_peak.get(self.phase, 0)
        self.python_peak[self.phase] = max(old, total)


class Arena:
    """Fixed capacity, explicit placeholder slots, paid full-word transfers.

    Unused payload is uninitialized: Python None is an allocator placeholder,
    not a preinitialized x/descriptor record. Every slot reservation and release
    is paid; live records get width writes. All head slots get paid zero writes.
    """
    def __init__(self, m, capacity, width, name, fill=None):
        self.m, self.capacity, self.width, self.name = m, capacity, width, name
        self.data = []
        self.released = False
        m.live.append(self)
        m.tick('allocation_header')
        for _ in m.indices(capacity):
            m.tick('allocator_slot_initialize')
            self.data.append(None)
        if not m.eq(fill, None):
            for i in m.indices(capacity):
                self.set(i, fill)
        m.sample_storage()

    def get(self, i, kind='array_word_read'):
        if not self.m.lt(i, self.capacity) or self.m.lt(i, 0):
            raise Invalid('array read bounds: ' + self.name)
        self.m.tick(kind, self.width)
        return self.data[i]

    def set(self, i, value, kind='array_word_write'):
        if not self.m.lt(i, self.capacity) or self.m.lt(i, 0):
            raise Invalid('array write bounds: ' + self.name)
        self.m.tick(kind, self.width)
        self.data[i] = value

    def release(self):
        if self.m.eq(self.released, True):
            return
        for i in self.m.indices(self.capacity):
            self.m.tick('array_slot_release')
            self.data[i] = None
        self.m.tick('allocation_release_header')
        self.data.clear()
        self.released = True
        self.m.live.remove(self)


def release_all(m, arenas):
    # Fixed owner list is instrumentation. Actual dynamic slot walks are paid.
    for i in m.indices(len(arenas)):
        m.tick('owner_array_read')
        arenas[i].release()


class Field:
    def __init__(self, m, modulus, domain):
        self.m, self.modulus, self.domain = m, modulus, domain

    def add(self, a, b):
        self.m.tick(self.domain + '_A')
        return (a + b) % self.modulus

    def sub(self, a, b):
        self.m.tick(self.domain + '_A')
        return (a - b) % self.modulus

    def mul(self, a, b):
        self.m.tick(self.domain + '_M')
        return (a * b) % self.modulus

    def square(self, a):
        self.m.tick(self.domain + '_S')
        return (a * a) % self.modulus

    def inverse(self, value):
        m = self.m
        if m.eq(value, 0):
            raise Invalid('zero inverse')
        row = m.inverses.setdefault(m.phase + '/' + self.domain,
             {'domain': self.domain, 'phase': m.phase, 'attempted': 0,
              'completed': 0, 'completed_M': 0, 'completed_S': 0,
              'interrupted_M': 0, 'interrupted_S': 0})
        row['attempted'] += 1
        before_m = m.kinds.get(self.domain + '_M', 0)
        before_s = m.kinds.get(self.domain + '_S', 0)
        complete = False
        try:
            exponent = m.sub(self.modulus, 2)
            bits, temp = 0, exponent
            while not m.eq(temp, 0):
                bits = m.add(bits, 1)
                temp = m.shr(temp, 1)
            answer, j = 1, m.sub(bits, 1)
            while m.le(0, j):
                answer = self.square(answer)
                if not m.eq(m.band(m.shr(exponent, j), 1), 0):
                    answer = self.mul(answer, value)
                j = m.sub(j, 1)
            complete = True
            row['completed'] += 1
            return answer
        finally:
            prefix = 'completed_' if complete else 'interrupted_'
            row[prefix + 'M'] += m.kinds.get(self.domain + '_M', 0) - before_m
            row[prefix + 'S'] += m.kinds.get(self.domain + '_S', 0) - before_s


class Curve:
    def __init__(self, m, fixture):
        self.m = m
        self.p, self.a, self.b, self.q, gx, gy = fixture
        self.f, self.sf = Field(m, self.p, 'Fp'), Field(m, self.q, 'Fq')
        self.g = (gx, gy)

    def x(self, p): return self.m.record(p, 0)
    def y(self, p): return self.m.record(p, 1)
    def identity(self, p): return self.m.eq(p, None)

    def equal(self, p, q):
        if self.identity(p):
            return self.identity(q)
        if self.identity(q):
            return False
        return self.m.eq(self.x(p), self.x(q)) and self.m.eq(self.y(p), self.y(q))

    def neg(self, p):
        if self.identity(p):
            return None
        return (self.x(p), self.f.sub(0, self.y(p)))

    def member(self, p):
        if self.identity(p):
            return True
        f, x, y = self.f, self.x(p), self.y(p)
        return self.m.eq(f.square(y), f.add(f.add(f.mul(f.square(x), x),
                                                        f.mul(self.a, x)), self.b))

    def add(self, p, q):
        """Ordinary complete affine addition, independent of paired kernel."""
        m, f = self.m, self.f
        if self.identity(p): return q
        if self.identity(q): return p
        x1, y1, x2, y2 = self.x(p), self.y(p), self.x(q), self.y(q)
        if m.eq(x1, x2):
            if m.eq(f.add(y1, y2), 0):
                return None
            if not m.eq(y1, y2):
                raise Invalid('equal-x inputs outside curve')
            m.tick('exception_tangent')
            num, den = f.add(f.mul(3, f.square(x1)), self.a), f.mul(2, y1)
        else:
            num, den = f.sub(y2, y1), f.sub(x2, x1)
        slope = f.mul(num, f.inverse(den))
        x3 = f.sub(f.square(slope), f.add(x1, x2))
        y3 = f.sub(f.mul(slope, f.sub(x1, x3)), y1)
        return (x3, y3)

    def scalar(self, scalar, point):
        m, acc, base = self.m, None, point
        if m.lt(scalar, 0): raise Invalid('negative scalar')
        while not m.eq(scalar, 0):
            if not m.eq(m.band(scalar, 1), 0):
                acc = self.add(acc, base)
            scalar = m.shr(scalar, 1)
            if not m.eq(scalar, 0): base = self.add(base, base)
        return acc

    def verify(self, scalar, target):
        self.m.tick('verification')
        return self.equal(self.scalar(scalar, self.g), target)


def prime(m, n):
    if m.lt(n, 2): return False
    d = 2
    while m.le(m.mul(d, d), n):
        if m.eq(m.rem(n, d), 0): return False
        d = m.add(d, 1)
    return True


def bit_width(m, largest):
    out = 1
    while m.lt(1, largest):
        largest = m.shr(largest, 1)
        out = m.add(out, 1)
    return out


def pow2ceil(m, n):
    value = 1
    while m.lt(value, n): value = m.mul(value, 2)
    return value


def ceiling_root(m, multiplier, n, factor=1):
    # Least r with factor*r*r >= multiplier*n; no floating-point/pow.
    target, lo, hi = m.mul(multiplier, n), 0, 1
    while m.lt(m.mul(factor, m.mul(hi, hi)), target): hi = m.mul(hi, 2)
    while m.lt(m.add(lo, 1), hi):
        mid = m.div(m.add(lo, hi), 2)
        if m.lt(m.mul(factor, m.mul(mid, mid)), target): lo = mid
        else: hi = mid
    return hi


def parameters(m, q):
    ell = 2
    while True:
        e2 = m.mul(ell, ell)
        e6 = m.mul(m.mul(e2, e2), e2)
        if m.le(m.mul(9, q), m.mul(4, e6)) and prime(m, ell): break
        ell = m.add(ell, 1)
    n = m.mul(2, m.mul(ell, ell))
    emax = ceiling_root(m, 9, q, 4)
    hc = pow2ceil(m, ceiling_root(m, 1, q))
    d = ceiling_root(m, 2, q)
    last = m.div(m.add(d, 1), 2)
    if not m.le(emax, m.mul(m.mul(ell, ell), ell)): raise Invalid('edge cap exceeds graph')
    return {'ell': ell, 'n': n, 'emax': emax, 'u': m.mul(2, emax),
            'hc': hc, 'd': d, 'last': last, 'qbits': bit_width(m, m.sub(q, 1))}


class Stream:
    def __init__(self, m, p, q, seed, tag, report):
        self.m = m
        self.state = m.rem(m.xor(m.xor(m.xor(tag, p), q), seed), 2**32)
        self.row = {'tag': tag, 'seed': seed, 'initial_state': self.state,
                    'draws': 0, 'rejects': 0, 'final_state': self.state}
        report.setdefault('streams', []).append(self.row)
        m.tick('field_record_write')

    def draw(self, n):
        m = self.m
        if not m.lt(0, n): raise Invalid('invalid RNG modulus')
        limit = m.sub(2**32, m.rem(2**32, n))
        while True:
            m.tick('field_record_read')
            self.state = m.rem(m.add(m.mul(1664525, self.state), 1013904223), 2**32)
            m.tick('field_record_write')
            word = m.xor(self.state, m.shr(self.state, 16))
            m.tick('rng_word')
            self.row['draws'] += 1
            self.row['final_state'] = self.state
            if m.lt(word, limit): return m.rem(word, n)
            m.tick('rng_rejection')
            self.row['rejects'] += 1


class Chain:
    def __init__(self, c, heads, capacity, node_width, eta, zeta, name):
        self.c, self.m, self.h, self.capacity = c, c.m, heads, capacity
        self.eta, self.zeta, self.used = eta, zeta, 0
        self.heads = Arena(c.m, heads, 1, name + '/heads', fill=-1)
        self.nodes = Arena(c.m, capacity, node_width, name + '/nodes')

    def slot(self, x):
        # Called only after explicit infinity dispatch.
        return self.m.rem(self.c.f.add(self.c.f.mul(self.eta, x), self.zeta), self.h)

    def query(self, slot, x):
        m = self.m
        node = self.heads.get(slot, 'head_read')
        while not m.eq(node, -1):
            m.tick('chain_probe')
            row = self.nodes.get(node, 'node_read')
            if m.eq(m.record(row, 0), x):
                m.tick('exact_match')
                return row
            node = m.record(row, self.m.sub(self.nodes.width, 1))
        return None

    def insert(self, slot, x, descriptor, known_head=None):
        m = self.m
        if not m.lt(self.used, self.capacity): raise Invalid('archive capacity exceeded')
        head = self.heads.get(slot, 'head_read') if m.eq(known_head, None) else known_head
        # descriptor is a fixed-schema register tuple (root index; edge,sign; index).
        m.tick('field_record_read', len(descriptor))
        self.nodes.set(self.used, (x, *descriptor, head), 'node_write')
        self.heads.set(slot, self.used, 'head_write')
        self.used = m.add(self.used, 1)

    def query_insert(self, slot, x, descriptor):
        # Candidate reuses its original head read for insertion.
        m = self.m
        head = self.heads.get(slot, 'head_read')
        node = head
        while not m.eq(node, -1):
            m.tick('chain_probe')
            row = self.nodes.get(node, 'node_read')
            if m.eq(m.record(row, 0), x):
                m.tick('exact_match')
                return row
            node = m.record(row, m.sub(self.nodes.width, 1))
        self.insert(slot, x, descriptor, head)
        return None

    def release(self):
        release_all(self.m, (self.heads, self.nodes))


def hash_parameters(c, seed, arm_id, report):
    rng = Stream(c.m, c.p, c.q, seed, c.m.xor(TAGS['hash'], arm_id), report)
    return c.m.add(1, rng.draw(c.m.sub(c.p, 1))), rng.draw(c.p)


def edge(m, ell, ordinal):
    m.tick('descriptor_decode')
    e2 = m.mul(ell, ell)
    s, rest = m.div(ordinal, e2), m.rem(ordinal, e2)
    t, x = m.div(rest, ell), m.rem(rest, ell)
    # Algebraically equivalent lexicographic recurrence; no prebuilt edge list.
    y = m.rem(m.add(m.mul(s, x), t), ell)
    return m.add(m.mul(x, ell), y), m.add(e2, m.add(m.mul(s, ell), t))


class Scratch:
    def __init__(self, m, b, name):
        self.m, self.b = m, b
        self.fp = Arena(m, m.mul(10, b), 1, name + '/field')
        self.ints = Arena(m, m.mul(2, b), 1, name + '/integer')

    def pos(self, section, i): return self.m.add(self.m.mul(section, self.b), i)
    def put(self, section, i, value): self.fp.set(self.pos(section, i), value)
    def get(self, section, i): return self.fp.get(self.pos(section, i))
    def release(self): release_all(self.m, (self.fp, self.ints))


def inverse_totals(m, domain):
    # Instrumentation snapshot, not numerical solver work.
    rows = [v for v in m.inverses.values() if v['domain'] == domain]
    return (sum(r['completed'] for r in rows), sum(r['completed_M'] for r in rows),
            sum(r['completed_S'] for r in rows))


def arithmetic_snapshot(m):
    return (m.kinds.get('Fp_M', 0), m.kinds.get('Fp_S', 0),
            m.kinds.get('Fp_A', 0), inverse_totals(m, 'Fp'))


def check_component(m, before, b, full, name):
    after = arithmetic_snapshot(m)
    inv = tuple(a - z for a, z in zip(after[3], before[3]))
    got = (after[0] - before[0] - inv[1], after[1] - before[1] - inv[2],
           after[2] - before[2], inv[0])
    expected = (5*b-3, b if full else 2*b, 6*b, 1) if b else (0, 0, 0, 0)
    row = {'phase': m.phase, 'component': name, 'pairs': b,
           'full_addition': full, 'observed_M_S_A_I': got, 'expected_M_S_A_I': expected,
           'completed_inverse_expansion_M_S': inv[1:], 'pass': got == expected}
    m.components.append(row)
    if got != expected: raise Invalid('regular arithmetic subtotal mismatch: ' + name)


def regular_batch(c, b, pair, scratch, full=False, name='paired'):
    """pair(i) returns immutable source points; outputs in scratch sections3,4.

    Defensive checks are charged before the coordinate boundary. Prefix product
    + backward sweep uses exactly3(b-1)M; no extra terminal multiply. Denominator
    orientation is x1-x2. Shared x1+x2 gives exactly6A for both kernel types.
    """
    m, f = c.m, c.f
    for i in m.indices(b):
        p, q = pair(i)
        if c.identity(p) or c.identity(q) or m.eq(c.x(p), c.x(q)):
            raise Invalid('nonregular input at regular boundary: ' + name)
    before = arithmetic_snapshot(m)
    for i in m.indices(b):
        p, q = pair(i)
        den = f.sub(c.x(p), c.x(q))
        scratch.put(0, i, den)
        scratch.put(1, i, den if m.eq(i, 0) else f.mul(scratch.get(1, m.sub(i, 1)), den))
    if m.eq(b, 0):
        check_component(m, before, b, full, name)
        return
    m.pending('batch_inverse', component=name, pairs=b)
    inv = f.inverse(scratch.get(1, m.sub(b, 1)))
    i = m.sub(b, 1)
    while m.lt(0, i):
        scratch.put(2, i, f.mul(inv, scratch.get(1, m.sub(i, 1))))
        inv = f.mul(inv, scratch.get(0, i))
        i = m.sub(i, 1)
    scratch.put(2, 0, inv)
    for i in m.indices(b):
        p, q = pair(i)
        x1, y1, x2, y2 = c.x(p), c.y(p), c.x(q), c.y(q)
        den_inv = scratch.get(2, i)
        slope_plus = f.mul(f.sub(y1, y2), den_inv)
        shared = f.add(x1, x2)
        plus = f.sub(f.square(slope_plus), shared)
        scratch.put(3, i, plus)
        if m.eq(full, True):
            scratch.put(4, i, f.sub(f.mul(slope_plus, f.sub(x1, plus)), y1))
        else:
            slope_minus = f.mul(f.add(y1, y2), den_inv)
            scratch.put(4, i, f.sub(f.square(slope_minus), shared))
    check_component(m, before, b, full, name)
    m.sample_storage()


def reference_batch(c, b, pair, scratch, reference_phase, full=False):
    """No cache or mutable output; returns only pass/fail after every output.

    Fixed-register immutable copies separate reference reads and arithmetic from
    solver state; no reference point can be stored by the caller in solver arrays.
    """
    with c.m.scope(reference_phase):
        for i in c.m.indices(b):
            left, right = pair(i)
            p = None if c.identity(left) else (c.x(left), c.y(left))
            q = None if c.identity(right) else (c.x(right), c.y(right))
            first, second = scratch.get(3, i), scratch.get(4, i)
            plus = c.add(p, q)
            if c.identity(plus) or not c.m.eq(first, c.x(plus)): return False
            if c.m.eq(full, True):
                if not c.m.eq(second, c.y(plus)): return False
            else:
                minus = c.add(p, c.neg(q))
                if c.identity(minus) or not c.m.eq(second, c.x(minus)): return False
    return True



def reference_candidate_batch(c, par, roots, first, b, scratch, reference_phase):
    """Independent ordinal/index validation plus immutable affine checks.

    Decoded expected indices are confined to this checker; only the final bool
    reaches candidate control flow. This detects consistent arithmetic on a
    wrongly ordered iterator edge as well as wrong paired coordinates.
    """
    m = c.m
    with m.scope(reference_phase):
        for r in m.indices(b):
            expected_i, expected_j = edge(m, par['ell'], m.add(first, r))
            actual_i = scratch.ints.get(m.mul(2, r))
            actual_j = scratch.ints.get(m.add(m.mul(2, r), 1))
            if not m.eq(expected_i, actual_i) or not m.eq(expected_j, actual_j):
                return False
        def expected_pair(r):
            i, j = edge(m, par['ell'], m.add(first, r))
            return root_point(m, roots, i), root_point(m, roots, j)
        return reference_batch(c, b, expected_pair, scratch, reference_phase)


def recover(c, target, labels, old_labels, report):
    """Both signs are attempted in +1,-1 order, including zero first divisor."""
    m, sf = c.m, c.sf
    a, b = labels
    aa, bb = old_labels
    for orientation in m.indices(2):
        sigma = 1 if m.eq(orientation, 0) else -1
        m.tick('recovery_orientation')
        den = sf.sub(b, bb) if m.eq(sigma, 1) else sf.add(b, bb)
        if m.eq(den, 0):
            report.setdefault('recovery_attempts', []).append({'sigma': sigma, 'zero_denominator': True})
            continue
        num = sf.sub(aa, a) if m.eq(sigma, 1) else sf.sub(sf.sub(0, aa), a)
        candidate = sf.mul(num, sf.inverse(den))
        ok = c.verify(candidate, target)
        report.setdefault('recovery_attempts', []).append({'sigma': sigma, 'verified': ok})
        if ok: return candidate
    return None


def zero_recover(c, target, labels, report):
    a, b = labels
    if c.m.eq(b, 0):
        report['null_zero'] = True
        return None
    proposal = c.sf.mul(c.sf.sub(0, a), c.sf.inverse(b))
    return proposal if c.verify(proposal, target) else None


def leaf_labels(c, par, roots, ordinal, sign):
    m, sf = c.m, c.sf
    i, j = edge(m, par['ell'], ordinal)
    ri, rj = roots.get(i), roots.get(j)
    a, b = m.record(ri, 1), m.record(ri, 2)
    aa, bb = m.record(rj, 1), m.record(rj, 2)
    if m.eq(sign, 1): return sf.add(a, aa), sf.add(b, bb)
    return sf.sub(a, aa), sf.sub(b, bb)


def root_point(m, roots, index): return m.record(roots.get(index), 0)


def generate_roots(c, target, seed, par, report, owner):
    m, bits = c.m, par['qbits']
    roots = Arena(m, par['n'], 5, owner + '/roots')
    powers_g = Arena(m, bits, 3, owner + '/powers_G')
    powers_q = Arena(m, bits, 3, owner + '/powers_Q')
    rng = Stream(m, c.p, c.q, seed, TAGS['labels'], report)
    pg, pq = c.g, target
    for j in m.indices(bits):
        powers_g.set(j, pg)
        powers_q.set(j, pq)
        if m.lt(m.add(j, 1), bits): pg, pq = c.add(pg, pg), c.add(pq, pq)
    for i in m.indices(par['n']):
        m.pending('eager_root', vertex=i, vertices=par['n'])
        a, b, acc = rng.draw(c.q), rng.draw(c.q), None
        for j in m.indices(bits):
            if not m.eq(m.band(m.shr(a, j), 1), 0): acc = c.add(acc, powers_g.get(j))
            if not m.eq(m.band(m.shr(b, j), 1), 0): acc = c.add(acc, powers_q.get(j))
        roots.set(i, (acc, a, b))  # five payload words: x,y,identity,a,b
    m.sample_storage()
    release_all(m, (powers_g, powers_q))
    report['all_roots_constructed'] = True
    return roots


def candidate(c, target, seed, par, report, owner):
    m, arenas, index, archive, scratch = c.m, [], None, None, None
    report.update(status='pending', leaf_reached=False, stop_class=None, arm_id=0)
    with m.scope(owner + '/input'):
        m.pending('candidate_input')
        if c.identity(target):
            if not c.verify(0, target): raise Invalid('identity verification')
            report.update(status='complete', stop_class='input', reason='Q=O', scalar=0)
            return 0
    reason, answer = None, None
    with m.scope(owner + '/setup'):
        eta, zeta = hash_parameters(c, seed, 0, report)
        roots = generate_roots(c, target, seed, par, report, owner)
        arenas.append(roots)
    with m.scope(owner + '/seed'):
        index = Chain(c, pow2ceil(m, par['n']), par['n'], 3, eta, zeta, owner + '/seed_index')
        for i in m.indices(par['n']):
            m.pending('seed_scan', vertex=i)
            root = roots.get(i)
            point = m.record(root, 0)
            labels = (m.record(root, 1), m.record(root, 2))
            if c.identity(point):
                answer = zero_recover(c, target, labels, report)
                reason = 'seed_zero_success' if not m.eq(answer, None) else 'seed_zero_unrecoverable'
                break
            x = c.x(point)
            match = index.query_insert(index.slot(x), x, (i,))
            if not m.eq(match, None):
                old = roots.get(m.record(match, 1))
                answer = recover(c, target, labels, (m.record(old, 1), m.record(old, 2)), report)
                reason = 'seed_match_success' if not m.eq(answer, None) else 'seed_match_unrecoverable'
                break
        index.release()
        index = None
    if m.eq(reason, None):
        report['leaf_reached'] = True
        with m.scope(owner + '/leaf'):
            archive = Chain(c, par['hc'], par['u'], 4, eta, zeta, owner + '/archive')
            scratch = Scratch(m, par['ell'], owner + '/scratch')
            start, graph_s, graph_t, graph_x, graph_y = 0, 0, 0, 0, 0
            e2 = m.mul(par['ell'], par['ell'])
            graph_point_base, graph_line_base = 0, e2
            while m.lt(start, par['emax']):
                remaining = m.sub(par['emax'], start)
                b = remaining if m.lt(remaining, par['ell']) else par['ell']
                # Sequential (s,t,x) graph enumeration: y advances by s in-row.
                for r in m.indices(b):
                    iv = m.add(graph_point_base, graph_y)
                    jv = graph_line_base
                    scratch.ints.set(m.mul(2, r), iv)
                    scratch.ints.set(m.add(m.mul(2, r), 1), jv)
                    graph_y = m.rem(m.add(graph_y, graph_s), par['ell'])
                    graph_x = m.add(graph_x, 1)
                    graph_point_base = m.add(graph_point_base, par['ell'])
                    if m.eq(graph_x, par['ell']):
                        graph_x, graph_t = 0, m.add(graph_t, 1)
                        graph_point_base = 0
                        graph_line_base = m.add(graph_line_base, 1)
                        if m.eq(graph_t, par['ell']): graph_t, graph_s = 0, m.add(graph_s, 1)
                        graph_y = graph_t
                def pair(r):
                    i = scratch.ints.get(m.mul(2, r))
                    j = scratch.ints.get(m.add(m.mul(2, r), 1))
                    return root_point(m, roots, i), root_point(m, roots, j)
                m.pending('candidate_leaf_batch', first_edge=start, edges=b)
                regular_batch(c, b, pair, scratch, name='candidate_leaf')
                if not reference_candidate_batch(c, par, roots, start, b, scratch, owner + '/reference'):
                    raise Invalid('candidate prepaid leaf reference mismatch')
                report['generated_leaf_keys'] = report.get('generated_leaf_keys', 0) + 2*b
                hit = False
                for t in m.indices(b):
                    ordinal = m.add(start, t)
                    for orientation in m.indices(2):
                        sign = 1 if m.eq(orientation, 0) else -1
                        section = m.add(3, orientation)
                        m.tick('sign_dispatch')
                        x = scratch.get(section, t)
                        m.pending('candidate_leaf_lookup', edge=ordinal, sign=sign)
                        report['inspected_leaf_keys'] = report.get('inspected_leaf_keys', 0) + 1
                        match = archive.query_insert(archive.slot(x), x, (ordinal, sign))
                        if not m.eq(match, None):
                            labels = leaf_labels(c, par, roots, ordinal, sign)
                            old_labels = leaf_labels(c, par, roots, m.record(match, 1), m.record(match, 2))
                            answer = recover(c, target, labels, old_labels, report)
                            reason = 'leaf_match_success' if not m.eq(answer, None) else 'leaf_match_unrecoverable'
                            hit = True
                            break
                    if m.eq(hit, True): break
                if m.eq(hit, True): break
                start = m.add(start, b)
            if m.eq(reason, None): reason = 'edge_cap'
    with m.scope(owner + '/release'):
        m.pending('candidate_release', reason=reason)
        if not m.eq(archive, None): archive.release()
        if not m.eq(scratch, None): scratch.release()
        release_all(m, arenas)
    report['candidate_reason'] = reason
    if m.eq(answer, None):
        report['stop_class'] = 'fallback'
        report['fallback'] = {'status': 'pending'}
        answer = fallback(c, target, seed, par, report['fallback'], owner + '/fallback')
    else:
        report['stop_class'] = 'leaf' if report['leaf_reached'] else 'seed'
    report.update(status='complete', scalar=answer, reason=reason)
    return answer


class Prefix:
    """One role's contiguous block generator, advanced only on demand."""
    def __init__(self, c, base, step, k, ell, owner, reference_phase):
        self.c, self.m, self.base, self.step = c, c.m, base, step
        self.k, self.ell, self.owner, self.ref = k, ell, owner, reference_phase
        self.w = self.m.add(self.m.mul(2, ell), 1)
        self.b = self.m.mul(k, self.w)
        self.centers = Arena(self.m, k, 3, owner + '/centers')
        self.offsets = Arena(self.m, ell, 3, owner + '/offsets')
        self.buffer = Arena(self.m, self.b, 2, owner + '/outputs')
        self.scratch = Scratch(self.m, k, owner + '/scratch')
        self.regular = Arena(self.m, k, 1, owner + '/regular_indices')
        self.first, self.has_block = 0, False
        for u in self.m.indices(ell):
            self.offsets.set(u, c.scalar(self.m.add(u, 1), step))
        for j in self.m.indices(k):
            index = self.m.add(ell, self.m.mul(j, self.w))
            self.centers.set(j, c.add(base, c.scalar(index, step)))
        self.stride = c.scalar(self.b, step)
        self.m.sample_storage()

    def classify(self, offset):
        count = 0
        for j in self.m.indices(self.k):
            p = self.centers.get(j)
            if not self.c.identity(p) and not self.c.identity(offset) and not self.m.eq(self.c.x(p), self.c.x(offset)):
                self.regular.set(count, j)
                count = self.m.add(count, 1)
        return count

    def advance(self):
        m, c = self.m, self.c
        count = self.classify(self.stride)
        def pair(i): return self.centers.get(self.regular.get(i)), self.stride
        regular_batch(c, count, pair, self.scratch, full=True, name='H019_advance')
        if not reference_batch(c, count, pair, self.scratch, self.ref, full=True):
            raise Invalid('H019 advance reference mismatch')
        # Exceptional additions precede mutation of regular centers.
        for j in m.indices(self.k):
            point = self.centers.get(j)
            if c.identity(point) or c.identity(self.stride) or m.eq(c.x(point), c.x(self.stride)):
                m.tick('exception_advance')
                self.centers.set(j, c.add(point, self.stride))
        for i in m.indices(count):
            self.centers.set(self.regular.get(i), (self.scratch.get(3, i), self.scratch.get(4, i)))
        self.first = m.add(self.first, self.b)

    def generate(self):
        m, c = self.m, self.c
        m.pending('H019_block', role=self.owner, first_index=self.first, block_size=self.b)
        if m.eq(self.has_block, True): self.advance()
        for j in m.indices(self.k):
            center = self.centers.get(j)
            pos = m.add(self.ell, m.mul(j, self.w))
            self.buffer.set(pos, (None if c.identity(center) else c.x(center), c.identity(center)))
        for u0 in m.indices(self.ell):
            u, offset = m.add(u0, 1), self.offsets.get(u0)
            count = self.classify(offset)
            def pair(i): return self.centers.get(self.regular.get(i)), offset
            regular_batch(c, count, pair, self.scratch, name='H019_side')
            if not reference_batch(c, count, pair, self.scratch, self.ref):
                raise Invalid('H019 prepaid side reference mismatch')
            for j in m.indices(self.k):
                point = self.centers.get(j)
                if c.identity(point) or c.identity(offset) or m.eq(c.x(point), c.x(offset)):
                    m.tick('exception_side_pair')
                    plus, minus = c.add(point, offset), c.add(point, c.neg(offset))
                    pos = m.add(self.ell, m.mul(j, self.w))
                    self.buffer.set(m.add(pos, u), (None if c.identity(plus) else c.x(plus), c.identity(plus)))
                    self.buffer.set(m.sub(pos, u), (None if c.identity(minus) else c.x(minus), c.identity(minus)))
            for i in m.indices(count):
                j = self.regular.get(i)
                pos = m.add(self.ell, m.mul(j, self.w))
                self.buffer.set(m.add(pos, u), (self.scratch.get(3, i), False))
                self.buffer.set(m.sub(pos, u), (self.scratch.get(4, i), False))
        self.has_block = True
        m.sample_storage()

    def get(self, index):
        m = self.m
        if not m.eq(self.has_block, True) or not m.lt(index, m.add(self.first, self.b)):
            self.generate()
        if m.lt(index, self.first): raise Invalid('noncontiguous H019 buffer request')
        return self.buffer.get(m.sub(index, self.first))

    def release(self):
        release_all(self.m, (self.centers, self.offsets, self.buffer, self.regular))
        self.scratch.release()


def baseline(c, target, seed, par, config, heads, arm_id, report, owner):
    m, k, ell = c.m, config[0], config[1]
    report.update(status='pending', configuration=[k, ell], heads=heads, arm_id=arm_id,
                  policy='fixed contiguous per-index baby then giant')
    with m.scope(owner + '/input'):
        m.pending('H019_input')
        if c.identity(target):
            if not c.verify(0, target): raise Invalid('H019 identity verification')
            report.update(status='complete', scalar=0, reason='Q=O')
            return 0
    with m.scope(owner + '/setup'):
        eta, zeta = hash_parameters(c, seed, arm_id, report)
        dg = c.scalar(par['d'], c.g)
        giant_step = c.neg(dg)
        baby = Prefix(c, None, c.g, k, ell, owner + '/baby', owner + '/reference')
        giant = Prefix(c, target, giant_step, k, ell, owner + '/giant', owner + '/reference')
        role_heads = m.div(heads, 2)
        capacity = m.add(par['last'], 1)
        bt = Chain(c, role_heads, capacity, 3, eta, zeta, owner + '/baby_table')
        gt = Chain(c, role_heads, capacity, 3, eta, zeta, owner + '/giant_table')
    answer, reason = None, None
    with m.scope(owner + '/search'):
        for i in m.indices(m.add(par['last'], 1)):
            for role in m.indices(2):
                m.tick('role_dispatch')
                m.pending('H019_lookup', index=i, role=role)
                values = baby.get(i) if m.eq(role, 0) else giant.get(i)
                x, infinity = m.record(values, 0), m.record(values, 1)
                report['inspected_keys'] = report.get('inspected_keys', 0) + 1
                if m.eq(infinity, True):
                    if m.eq(role, 0):
                        # Includes any wrap identity; never treat baby O as Q.
                        continue
                    proposal = c.sf.mul(i, par['d'])
                    if not c.verify(proposal, target): raise Invalid('giant infinity recovery')
                    answer, reason = proposal, 'giant_infinity'
                    break
                own, other = (bt, gt) if m.eq(role, 0) else (gt, bt)
                slot = own.slot(x)  # One shared affine hash evaluation for both roles.
                match = other.query(slot, x)
                if not m.eq(match, None):
                    old = m.record(match, 1)
                    bi, gi = (i, old) if m.eq(role, 0) else (old, i)
                    jd = c.sf.mul(gi, par['d'])
                    for orientation in m.indices(2):
                        sign = 1 if m.eq(orientation, 0) else -1
                        m.tick('recovery_orientation')
                        proposal = c.sf.add(jd, bi) if m.eq(sign, 1) else c.sf.sub(jd, bi)
                        ok = c.verify(proposal, target)
                        report.setdefault('recovery_attempts', []).append({'sigma': sign, 'verified': ok})
                        if ok:
                            answer, reason = proposal, 'cross_role_match'
                            break
                    if m.eq(answer, None): raise Invalid('unrecoverable H019 geometric equality')
                    break
                own.insert(slot, x, (i,))
            if not m.eq(answer, None): break
        if m.eq(answer, None): raise Invalid('H019 full prefix failed to recover target')
        report['generated_keys'] = (baby.first + baby.b if baby.has_block else 0) + (giant.first + giant.b if giant.has_block else 0)
        report['discarded_out_of_cap_keys'] = max(0, (baby.first + baby.b if baby.has_block else 0) - (par['last'] + 1)) + max(0, (giant.first + giant.b if giant.has_block else 0) - (par['last'] + 1))
        report['final_advance_policy'] = 'no advance after stopping; prior advances paid on demand'
        m.sample_storage()
    with m.scope(owner + '/release'):
        m.pending('H019_release')
        baby.release()
        giant.release()
        bt.release()
        gt.release()
    report.update(status='complete', scalar=answer, reason=reason)
    return answer


def fallback(c, target, seed, par, report, owner):
    m = c.m
    report['status'] = 'pending'
    with m.scope(owner + '/shift'):
        m.pending('fallback_shift')
        rng = Stream(m, c.p, c.q, seed, TAGS['fallback'], report)
        shift = rng.draw(c.q)
        shifted = c.add(target, c.scalar(shift, c.g))
        report['shift'] = shift
    report['primary'] = {'status': 'pending'}
    # Configuration is frozen by public fixture q, not observed cost or secret.
    with m.scope(owner + '/public_configuration'):
        config = None
        for fixture_index in m.indices(4):
            m.tick('configuration_read')
            if m.eq(FIXTURES[fixture_index][3], c.q):
                config = CONFIGS[fixture_index][0]
                break
        if m.eq(config, None): raise Invalid('no frozen primary configuration')
    answer = baseline(c, shifted, seed, par, config, par['hc'], 1,
                      report['primary'], owner + '/primary')
    with m.scope(owner + '/unshift'):
        m.pending('fallback_unshift_and_verify')
        answer = c.sf.sub(answer, shift)
        if not c.verify(answer, target): raise Invalid('blinded fallback final verification')
    report.update(status='complete', scalar=answer)
    return answer


def capacities(c, par, configs):
    """Public-only packed model, paid calculations before any solver arm.

    128 fixed 64-bit work registers (including RNG, scalar/inverse transient,
    reference copies, descriptor arithmetic, point temporaries) are reserved at
    every stage. Arena header is64+pointer-width bits. No packed bit layout is
    actually implemented by Python. Narrow payload bits are separately rounded
    into64-bit words per array; metadata/head/next null codes are included.
    """
    m = c.m
    pbits, qbits = bit_width(m, m.sub(c.p, 1)), par['qbits']
    regs = m.mul(128, 64)
    def array(name, count, bits, payload='live or uninitialized capacity'):
        ptr = bit_width(m, count)
        header = m.add(64, ptr)
        packed = m.add(m.mul(count, bits), header)
        words = m.div(m.add(packed, 63), 64)
        return {'name': name, 'slots': count, 'bits_per_slot': bits,
                'packed_bits_including_header': packed, 'rounded_64bit_words': words,
                'unused_payload': payload, 'allocator_placeholders': 'one paid slot each'}
    def stage(name, arrays):
        total = regs
        words = m.div(regs, 64)
        for a in arrays:
            total = m.add(total, a['packed_bits_including_header'])
            words = m.add(words, a['rounded_64bit_words'])
        return {'stage': name, 'register_bits': regs, 'arrays': arrays,
                'packed_bits': total, 'rounded_64bit_words': words,
                'packed_bytes_ceiling': m.div(m.add(total, 7), 8)}
    pointbits = m.add(m.mul(2, pbits), 1)
    rootbits = m.add(pointbits, m.mul(2, qbits))
    roots = array('roots(x,y,identity,a,b)', par['n'], rootbits)
    power_g = array('G powers', qbits, pointbits)
    power_q = array('Q powers', qbits, pointbits)
    hn, un = pow2ceil(m, par['n']), par['n']
    seednode = m.add(m.add(pbits, bit_width(m, m.sub(un, 1))), bit_width(m, un))
    seedst = stage('seed index', [roots, array('seed heads', hn, bit_width(m, un)),
                                          array('seed nodes(x,root,next)', un, seednode)])
    edgebits = bit_width(m, m.sub(par['emax'], 1))
    leafnode = m.add(m.add(m.add(pbits, edgebits), 1), bit_width(m, par['u']))
    scratchbits = m.maximum(m.maximum(pbits, qbits), bit_width(m, m.mul(10, par['ell'])))
    leafst = stage('leaf', [roots, array('leaf heads', par['hc'], bit_width(m, par['u'])),
                      array('leaf nodes(x,edge,sign,next)', par['u'], leafnode),
                      array('field scratch', m.mul(10, par['ell']), pbits),
                      array('integer scratch', m.mul(2, par['ell']), scratchbits)])
    setupst = stage('eager roots and powers', [roots, power_g, power_q])
    controls = []
    cap = m.add(par['last'], 1)
    for cfgno in m.indices(2):
        k, ell = configs[cfgno]
        b = m.mul(k, m.add(m.mul(2, ell), 1))
        for head_index in m.indices(3):
            multiplier = 1 if m.eq(head_index, 0) else 2 if m.eq(head_index, 1) else 4
            m.tick('configuration_read')
            heads = m.mul(multiplier, par['hc'])
            indexbits = bit_width(m, m.sub(cap, 1))
            nodebits = m.add(m.add(pbits, indexbits), bit_width(m, cap))
            arrays = []
            for role in m.indices(2):
                role_name = 'baby' if m.eq(role, 0) else 'giant'
                arrays.extend([array(role_name + ' node arena', cap, nodebits),
                    array(role_name + ' heads', m.div(heads, 2), bit_width(m, cap)),
                    array(role_name + ' full centers', k, pointbits),
                    array(role_name + ' full offsets', ell, pointbits),
                    array(role_name + ' output buffer(x,identity)', b, m.add(pbits, 1)),
                    array(role_name + ' field scratch', m.mul(10, k), pbits),
                    array(role_name + ' integer scratch', m.mul(2, k), scratchbits),
                    array(role_name + ' regular indices', k, bit_width(m, m.sub(k, 1)))])
            # Strides, DG, giant_step and base/step references are fixed registers;
            # their allowance is already included in the common128-word reserve.
            st = stage('H019 complete lifecycle', arrays)
            controls.append({'arm_id': m.add(16, m.add(m.mul(3, cfgno), head_index)),
                             'configuration': [k, ell], 'heads': heads, 'multiplier': multiplier,
                             'capacity': st})
    # Candidate lifecycle includes primary blinded fallback with shift registers.
    fallbackst = dict(controls[0]['capacity'])
    fallbackst['stage'] = 'released-candidate blinded primary fallback'
    stages = [setupst, seedst, leafst, fallbackst]
    peak = 0
    for st in stages: peak = m.maximum(peak, st['packed_bits'])
    for control in controls:
        control['admitted'] = m.le(control['capacity']['packed_bits'], peak)
        control['omission'] = None if control['admitted'] else 'declared packed peak exceeds candidate lifecycle peak'
    if not controls[0]['admitted']: raise Invalid('primary H019 does not fit declared candidate peak')
    return {'scope': 'logical packed payload plus null codes, arena headers and fixed registers; Python implements ordinary objects',
            'candidate_stages': stages, 'candidate_declared_peak_bits': peak,
            'candidate_declared_peak_bytes': m.div(m.add(peak, 7), 8),
            'controls': controls, 'primary': 'arm16 first configuration at Hc',
            'lower_envelope': 'descriptive only; never executable target-dependent choice',
            'word_model': '64-bit ceiling separately per array; packed bit widths are not uniform event prices',
            'metadata': 'immutable curve parameters and retained report/counter storage excluded from matched solver model',
            'register_bound': '128 fixed64-bit registers is a declared conservative allowance, not measured Python stack storage'}


def public_checks(c, par, configs, report, owner):
    m, g = c.m, c.g
    report['status'] = 'pending'
    with m.scope(owner + '/input'):
        m.pending('public_component_inputs')
        pairs = Arena(m, par['ell'], 6, owner + '/public_pairs')
        for i in m.indices(par['ell']): pairs.set(i, (c.scalar(m.add(i, 2), g), g))
        scratch = Scratch(m, par['ell'], owner + '/public_scratch')
        def pair(i): return pairs.get(i)
        regular_batch(c, par['ell'], pair, scratch, name='public_paired')
        if not reference_batch(c, par['ell'], pair, scratch, owner + '/reference'):
            raise Invalid('public paired kernel check')
        release_all(m, (pairs,))
        scratch.release()
        report['paired_regular'] = True
        # Distinct k values are public, fixed configurations. No cost-based tuning.
        for cfgno in m.indices(2):
            k = configs[cfgno][0]
            if not m.eq(cfgno, 0) and m.eq(k, configs[0][0]): continue
            pairs = Arena(m, k, 6, owner + '/full_pairs')
            for i in m.indices(k): pairs.set(i, (c.scalar(m.add(i, 2), g), g))
            scratch = Scratch(m, k, owner + '/full_scratch')
            def fullpair(i): return pairs.get(i)
            regular_batch(c, k, fullpair, scratch, full=True, name='public_full_addition')
            if not reference_batch(c, k, fullpair, scratch, owner + '/reference', full=True):
                raise Invalid('public full addition check')
            pairs.release()
            scratch.release()
        if not c.equal(c.add(None, g), g): raise Invalid('O support')
        if not c.equal(c.add(g, g), c.scalar(2, g)): raise Invalid('tangent dispatch')
        negative_g = c.neg(g)
        if not c.identity(c.add(g, negative_g)): raise Invalid('vertical dispatch')
        if not c.identity(c.add(g, c.neg(g))): raise Invalid('tangent pair minus dispatch')
        if not c.equal(c.add(g, c.neg(negative_g)), c.scalar(2, g)): raise Invalid('vertical pair minus dispatch')
        report['identity_tangent_vertical'] = True
        q2 = c.scalar(2, g)
        a1, a2 = c.sf.sub(0, 1), c.sf.sub(0, 3)
        # Construct and verify the public representation, without giving solver advice.
        if not c.equal(c.add(c.scalar(a1, g), q2), g): raise Invalid('public first label')
        if not c.equal(c.add(c.scalar(a2, g), q2), c.neg(g)): raise Invalid('public second label')
        recovery = {}
        result = recover(c, q2, (a1, 1), (a2, 1), recovery)
        if not m.eq(result, 2): raise Invalid('second signed orientation required')
        report['zero_first_denominator_recovery'] = recovery
        null = {}
        if not m.eq(zero_recover(c, q2, (0, 0), null), None): raise Invalid('null zero recovery')
        same = {}
        if not m.eq(recover(c, q2, (1, 0), (1, 0), same), None): raise Invalid('identical-label null recovery')
        report['null_zero_and_identical_labels'] = {'zero': null, 'identical': same}
    if m.eq(c.q, 73):
        report['forced_fallback_component'] = {'status': 'pending', 'classification': 'public forced component; not natural candidate failure'}
        answer = fallback(c, q2, 7, par, report['forced_fallback_component'], owner + '/forced_fallback')
        if not m.eq(answer, 2): raise Invalid('public forced fallback')
    report['status'] = 'complete'


def certify(c, report, owner):
    m, f = c.m, c.f
    with m.scope(owner + '/certification'):
        m.pending('fixture_certification')
        if not prime(m, c.p) or not prime(m, c.q): raise Invalid('public p or q not prime')
        disc = f.add(f.mul(4, f.mul(f.square(c.a), c.a)), f.mul(27, f.square(c.b)))
        if m.eq(disc, 0) or c.identity(c.g) or not c.member(c.g): raise Invalid('invalid public curve/G')
        if not c.identity(c.scalar(c.q, c.g)): raise Invalid('[q]G is not O')
        report['certification'] = {'p_prime': True, 'q_prime': True, 'nonsingular': True,
                                   'nonidentity_member_G': True, 'fresh_qG_is_O': True,
                                   'order_conclusion': 'prime q and nonidentity G certify order q'}


def run_arm(c, fn, report, expected, owner):
    report['status'] = 'pending'
    report['start_global_events'] = c.m.total
    c.m.report['active_arm'] = owner
    harness_checked = False
    try:
        answer = fn()
        report['solver_returned'] = True
        report['status'] = 'pending_harness_comparison'
        with c.m.scope(owner + '/harness_final_comparison'):
            if not c.m.eq(answer, expected): raise Invalid('returned scalar disagrees with private harness target')
        report['harness_scalar_match'] = True
        harness_checked = True
        report['status'] = 'complete'
        return answer
    finally:
        report['end_global_events'] = c.m.total
        report['consumed_events'] = c.m.total - report['start_global_events']
        if not harness_checked: report['status'] = 'incomplete'


def metadata():
    sources = [Path(__file__), HERE / 'protocol.md',
               HERE.parents[1] / 'findings' / 'H034-finite-contract.md',
               HERE.parents[1] / 'findings' / 'H034-matched-memory-cost-screen.md',
               HERE.parents[1] / 'findings' / 'H019-xonly-baseline-screen.md']
    hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    interpreter = Path(sys.executable).resolve()
    hashes[str(interpreter)] = hashlib.sha256(interpreter.read_bytes()).hexdigest()
    return {'hashes': hashes, 'support_modules': [], 'interpreter': str(interpreter),
            'python': sys.version, 'platform': platform.platform()}


def execute(output):
    # Exclusive create happens before any diagnostic work; existing path is refused.
    # A reserved valid pending report preserves evidence even if hard-killed later.
    report = {'protocol': 'H034-C4-v2', 'status': 'pending', 'pending': 'initialization',
              'event_cap': EVENT_CAP, 'internal_seconds': SECONDS_CAP,
              'outer_seconds': 60, 'fixtures': [], 'active_arm': None,
              'verified_improvement': 'NONE', 'baseline_exponent': '1/2',
              'interpretation': 'finite synthetic correctness/ledger diagnostic only',
              'admin_output': 'hashes, immutable report/counter bookkeeping, JSON and Python size observations excluded from event count; included in elapsed wall time',
              'memory_scope': 'packed model and approximate observed Python storage kept separate; neither is hardware traffic',
              'primitives': __doc__}
    with output.open('x', encoding='utf-8') as handle:
        json.dump(report, handle, indent=2)
        handle.flush()
        m = Meter(report)
        previous = signal.getsignal(signal.SIGTERM)
        def term(_signum, _frame):
            m.guard = 'external_SIGTERM'
            raise Halt('external SIGTERM; censored, no retry')
        signal.signal(signal.SIGTERM, term)
        try:
            report['metadata'] = metadata()
            # All capacity/omission decisions precede the very first solver arm.
            curves, params, capacities_rows = [], [], []  # Harness public records only.
            for fi, values in enumerate(FIXTURES):
                fr = {'fixture': list(values), 'index': fi, 'status': 'pending',
                      'public_checks': {'status': 'untested'}, 'explicit_cases': [],
                      'sampled_cases': [{'seed': s, 'status': 'untested', 'candidate': {'status': 'untested'},
                                         'controls': [{'arm_id': a, 'status': 'untested'} for a in range(16, 22)]}
                                        for s in SEEDS]}
                report['fixtures'].append(fr)
                c = Curve(m, values)
                with m.scope('fixture' + str(fi) + '/capacity'):
                    par = parameters(m, c.q)
                    parameter_names = ('ell', 'n', 'emax', 'u', 'hc', 'd', 'last')
                    for parameter_index in m.indices(7):
                        m.tick('public_parameter_read', 2)
                        if not m.eq(par[parameter_names[parameter_index]], EXPECTED[fi][parameter_index]):
                            raise Invalid('runtime public parameter mismatch')
                    cap = capacities(c, par, CONFIGS[fi])
                curves.append(c)
                params.append(par)
                capacities_rows.append(cap)
                fr['parameters'], fr['declared_capacity'] = par, cap
            report['capacity_table_complete_before_first_arm'] = True
            for fi, c in enumerate(curves):
                fr, par = report['fixtures'][fi], params[fi]
                owner = 'fixture' + str(fi)
                certify(c, fr, owner)
                public_checks(c, par, CONFIGS[fi], fr['public_checks'], owner + '/public')
            # Diagnostic O,G,-G cases are separate from sampled cases/averages.
            c, par, fr = curves[0], params[0], report['fixtures'][0]
            with m.scope('fixture0/explicit_input'):
                targets = ((None, 0, 'O'), (c.g, 1, 'G'), (c.neg(c.g), m.sub(c.q, 1), '-G'))
            for target, scalar, label in targets:
                row = {'label': label, 'seed': 7, 'status': 'pending', 'candidate': {'status': 'untested'},
                       'primary': {'status': 'untested'}, 'classification': 'explicit public diagnostic'}
                fr['explicit_cases'].append(row)
                owner = 'fixture0/explicit_' + label
                run_arm(c, lambda: candidate(c, target, 7, par, row['candidate'], owner + '/candidate'), row['candidate'], scalar, owner + '/candidate')
                run_arm(c, lambda: baseline(c, target, 7, par, CONFIGS[0][0], par['hc'], 16, row['primary'], owner + '/primary'), row['primary'], scalar, owner + '/primary')
                row['status'] = 'complete'
            for fi, c in enumerate(curves):
                fr, par, cap = report['fixtures'][fi], params[fi], capacities_rows[fi]
                for case in fr['sampled_cases']:
                    seed = case['seed']
                    owner = 'fixture' + str(fi) + '/seed' + str(seed)
                    case['status'] = 'pending'
                    with m.scope(owner + '/harness_input'):
                        m.pending('uniform_full_range_target', fixture=fi, seed=seed)
                        rng = Stream(m, c.p, c.q, seed, TAGS['target'], case)
                        secret = rng.draw(c.q)
                        target = c.scalar(secret, c.g)
                        case['private_harness_scalar'] = secret
                        case['public_target'] = target
                    run_arm(c, lambda: candidate(c, target, seed, par, case['candidate'], owner + '/candidate'),
                            case['candidate'], secret, owner + '/candidate')
                    for spec, arm in zip(cap['controls'], case['controls']):
                        arm['declared_capacity'] = spec['capacity']
                        if not spec['admitted']:
                            arm.update(status='omitted', reason=spec['omission'])
                            continue
                        name = owner + '/control' + str(spec['arm_id'])
                        run_arm(c, lambda: baseline(c, target, seed, par, spec['configuration'], spec['heads'],
                                                   spec['arm_id'], arm, name), arm, secret, name)
                    case['status'] = 'complete'
                fr['status'] = 'complete'
            report['status'] = 'completed_finite_diagnostic'
            report['pending'] = None
            report['active_arm'] = None
        except Halt as exc:
            report.update(status='censored_inconclusive', error=str(exc))
        except Invalid as exc:
            report.update(status='implementation_or_ledger_falsified', error=str(exc))
        except Exception as exc:
            report.update(status='implementation_error_inconclusive', error=type(exc).__name__ + ': ' + str(exc))
        finally:
            signal.signal(signal.SIGTERM, previous)
            # No cleanup after censorship: it would perform unbudgeted solver work.
            # Live partially allocated arrays are exposed as administrative evidence.
            m.sample_storage()
            report.update(events=m.total, event_categories=m.kinds, phase_event_categories=m.phases,
                          inverse_expansions=m.inverses, regular_components=m.components,
                          guard_fired=m.guard, elapsed_seconds=time.monotonic() - m.started,
                          observed_python_working_storage_bytes_by_phase=m.python_peak,
                          python_storage_limitation='recursive getsizeof samples of live Arena payloads plus arena objects; shared objects deduplicated; fixed-register stack, allocator overhead, instrumentation and retained reports excluded; not exact allocator peak',
                          live_arrays_at_stop=[{'name': a.name, 'capacity': a.capacity, 'width_words': a.width,
                                               'initialized_allocator_slots': len(a.data)} for a in m.live])
            for fr in report['fixtures']:
                for case in fr['sampled_cases']:
                    if case['status'] == 'pending': case['status'] = 'incomplete'
                for case in fr['explicit_cases']:
                    if case['status'] == 'pending': case['status'] = 'incomplete'
            handle.seek(0)
            json.dump(report, handle, indent=2)
            handle.write('\n')
            handle.truncate()
            handle.flush()
    return 0 if report['status'] == 'completed_finite_diagnostic' else 2


def main():
    parser = argparse.ArgumentParser(description='H034 fixed synthetic diagnostic; execution needs independent source review and separate root admission')
    parser.add_argument('--execute', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not args.execute or args.output is None:
        parser.error('requires --execute and --output; no numerical work was performed')
    try:
        return execute(args.output)
    except FileExistsError:
        print('Refusing existing output path; no run/retry performed: ' + str(args.output), file=sys.stderr)
        return 3


if __name__ == '__main__':
    sys.exit(main())
