#!/usr/bin/env python3
"""H030 C2 source-reviewed synthetic diagnostic; only --execute does work.

No full-size, complete-rho, timing, random-map, or improvement claim. The sole
runtime cap includes support imports, certification, diagnostics and solver work.
Record payload words (including pointers/flags) are explicit; local registers,
immutable curve parameters and counter/report administration are free. Point
coordinates are paid on every implemented attribute access. Dynamic arrays use
H018's paid accesses. No diagnostic coordinate is supplied to either solver.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROTOCOL = HERE / "c2_protocol.md"
SUPPORT_PATHS = (HERE.parent / "H018" / "bm_probe.py",
                 HERE.parent / "H028" / "key_probe.py")
FIXTURES = ((59, 28, 27, 73, 34, 35), (101, 2, 31, 103, 0, 43),
            (251, 1, 4, 271, 0, 2), (8191, 1, 5, 8053, 0, 789))
SEEDS = (7, 19)
EVENT_CAP, SECONDS_CAP = 1_000_000, 55.0
TAGS = {"jumps": 0x4A554D50, "targets": 0x54415247,
        "starts": 0x53544152, "hash": 0x48415348}


class Record:
    """All fixed-schema accesses paid; pointers/metadata are record words too."""
    def __init__(self, m, **values):
        self.m = m
        self.values = {}
        for key, value in values.items():
            m.tick("field_record_write")
            self.values[key] = value

    def __getitem__(self, key):
        self.m.tick("field_record_read")
        return self.values[key]

    def __setitem__(self, key, value):
        self.m.tick("field_record_write")
        self.values[key] = value


def size(m, seq):
    m.tick("array_length")
    return len(seq)


def xor(m, a, b):
    m.tick("bit_xor")
    return a ^ b


def stream(m, p, q, seed, tag):
    return Record(m, state=m.rem(xor(m, xor(m, xor(m, tag, p), q), seed), 2**32))


def draw(m, rng, n):
    limit = m.sub(2**32, m.rem(2**32, n))
    while True:
        s = m.rem(m.add(m.mul(1664525, rng["state"]), 1013904223), 2**32)
        rng["state"] = s
        u = xor(m, s, m.shr(s, 16))
        if m.lt(u, limit):
            return m.rem(u, n)


def canonical(curve, point, h=None):
    """Return point,h,sign; h=None selects y. Infinity precedes selection."""
    m, f = curve.m, curve.f
    if m.eq(point, None):
        return None, 0 if h is not None else None, 1
    selector = point.y if h is None or m.eq(h, 0) else h
    negative = f.sub(0, selector)
    sign = -1 if m.lt(negative, selector) else 1
    if m.eq(sign, -1):
        point = curve.neg(point)
        if h is not None:
            h = f.sub(0, h)
    return point, h, sign


def vector(m, index, sign):
    out = m.zeroes(8)
    m.write(out, index, sign)
    return out


def rank(m, v):
    """Arithmetic ranking of the frozen order; no inverse-point dictionary."""
    nonzero = []
    i = 0
    while m.lt(i, 8):
        value = m.read(v, i)
        if not m.eq(value, 0):
            m.append(nonzero, Record(m, index=i, value=value))
        i = m.add(i, 1)
    n = size(m, nonzero)
    if m.eq(n, 0):
        return 0
    if m.eq(n, 1):
        item = m.read(nonzero, 0)
        i, value = item["index"], item["value"]
        negative = 1 if m.lt(value, 0) else 0
        absolute = m.sub(0, value) if negative else value
        if not m.le(absolute, 2):
            raise ValueError("formal radius exceeded")
        return m.add(1 if m.eq(absolute, 1) else 17, m.add(m.mul(2, i), negative))
    if not m.eq(n, 2):
        raise ValueError("formal radius exceeded")
    first, second = m.read(nonzero, 0), m.read(nonzero, 1)
    i, a = first["index"], first["value"]
    j, b = second["index"], second["value"]
    if not (m.eq(m.mul(a, a), 1) and m.eq(m.mul(b, b), 1)):
        raise ValueError("invalid pair vector")
    preceding = m.div(m.mul(i, m.sub(15, i)), 2)
    pair = m.add(preceding, m.sub(m.sub(j, i), 1))
    signs = m.add(2 if m.lt(a, 0) else 0, 1 if m.lt(b, 0) else 0)
    return m.add(33, m.add(m.mul(4, pair), signs))


def copy_vector(m, v):
    out, i = [], 0
    while m.lt(i, 8):
        m.append(out, m.read(v, i))
        i = m.add(i, 1)
    return out


def descriptor(m, full=None, origin=None, offset=None, slope=None, sign=1):
    # Nine words: point pointer, origin pointer, offset pointer, slope, sign,
    # cached-x flag/value, cached-y flag/value. Referents are immutable points.
    return Record(m, full=full, origin=origin, offset=offset, slope=slope,
                  sign=sign, has_x=False, x=None, has_y=False, y=None)


def materialize(curve, desc, cache, full):
    """Validation calls cache=False: no mutation or solver savings."""
    m, f = curve.m, curve.f
    point = desc["full"]
    if not m.eq(point, None):
        return point if full else point.x
    slope = desc["slope"]
    if m.eq(slope, None):
        return None
    origin, offset = desc["origin"], desc["offset"]
    if desc["has_x"]:
        x = desc["x"]
    else:
        x = f.sub(f.sub(f.square(slope), origin.x), offset.x)
        if cache:
            desc["x"], desc["has_x"] = x, True
    if not full:
        return x
    if desc["has_y"]:
        y = desc["y"]
    else:
        y = f.sub(f.mul(slope, f.sub(origin.x, x)), origin.y)
        if m.eq(desc["sign"], -1):
            y = f.sub(0, y)
        if cache:
            desc["y"], desc["has_y"] = y, True
    point = curve.point(x, y)
    if cache:
        desc["full"] = point
    return point


def inverse_field(base, m, modulus, domain="Fp"):
    """Expanded field arithmetic plus independent attempted/completed I ledger."""
    class Field(base.Field):
        def add(self, a, b):
            m.tick("scalar_field_add" if domain == "Fq" else "field_add")
            return (a + b) % modulus
        def sub(self, a, b):
            m.tick("scalar_field_sub" if domain == "Fq" else "field_sub")
            return (a - b) % modulus
        def mul(self, a, b):
            m.tick("scalar_field_mul" if domain == "Fq" else "field_mul")
            return (a * b) % modulus
        def square(self, a):
            m.tick("scalar_field_square" if domain == "Fq" else "field_square")
            return (a * a) % modulus
        def inverse(self, value):
            phase = m.phase
            mk = "scalar_field_mul" if domain == "Fq" else "field_mul"
            sk = "scalar_field_square" if domain == "Fq" else "field_square"
            before_m = m.by_kind.get(mk, 0)
            before_s = m.by_kind.get(sk, 0)
            row = m.inverse_rows.setdefault(phase + "|" + domain,
                {"phase": phase, "domain": domain, "attempted": 0,
                 "completed": 0, "completed_M": 0, "completed_S": 0,
                 "interrupted_M": 0, "interrupted_S": 0})
            row["attempted"] += 1
            complete = False
            try:
                answer = super().inverse(value)
                row["completed"] += 1
                complete = True
                return answer
            finally:
                prefix = "completed_" if complete else "interrupted_"
                row[prefix + "M"] += m.by_kind.get(mk, 0) - before_m
                row[prefix + "S"] += m.by_kind.get(sk, 0) - before_s

    return Field(m, modulus)


def load_support():
    modules = []
    for i, path in enumerate(SUPPORT_PATHS):
        name = "h030_c2_support_" + str(i)
        spec = importlib.util.spec_from_file_location(name, path)
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        spec.loader.exec_module(module)  # Definitions only; no old main/execute.
        modules.append(module)
    return modules


def table_setup(base, key, curve, g, alpha, owner, report):
    m, f = curve.m, curve.f
    m.phase = owner + "/setup"
    entries, jumps = [], []
    report["working_memory_bounds"] = working_memory_bounds(owner)
    report["table_pending"] = True
    report["completed_jump_records"] = 0
    report["completed_formal_records"] = []
    hg = key.binary_h(curve, g, report["miller"], owner + ":G") if owner == "candidate" else None
    qf = inverse_field(base, m, curve.q, "Fq")
    i = 0
    limit = 8 if owner == "candidate" else 32
    while m.lt(i, limit):
        a = m.read(alpha, i)
        if owner == "candidate":
            point, h = curve.scalar_h(a, g, hg)
        else:
            point, h = curve.scalar(a, g), None
        m.append(jumps, Record(m, point=point, h=h, alpha=a) if owner == "candidate"
                 else Record(m, point=point, alpha=a))
        report["completed_jump_records"] = len(jumps)
        i = m.add(i, 1)
    if owner == "control":
        report["table_pending"] = False
        return jumps, None, None
    m.append(entries, Record(m, point=None, h=0, alpha=0, vector=m.zeroes(8),
                             parent=None, signed_jump=None))
    export_table(report, entries)
    i = 0
    while m.lt(i, 8):
        jump = m.read(jumps, i)
        sign = 1
        while m.le(-1, sign):
            point, h, a = jump["point"], jump["h"], jump["alpha"]
            if m.eq(sign, -1):
                point, h, a = curve.neg(point), f.sub(0, h), qf.sub(0, a)
            m.append(entries, Record(m, point=point, h=h, alpha=a,
                vector=vector(m, i, sign), parent=0, signed_jump=Record(m, index=i, sign=sign)))
            export_table(report, entries)
            sign = m.sub(sign, 2)
        i = m.add(i, 1)
    # Frozen doubled-unit order followed by lexicographic coordinate/sign pairs.
    i = 0
    while m.lt(i, 8):
        sign = 1
        while m.le(-1, sign):
            parent = m.add(1, m.add(m.mul(2, i), 1 if m.lt(sign, 0) else 0))
            append_composite(curve, qf, entries, parent, i, sign)
            export_table(report, entries)
            sign = m.sub(sign, 2)
        i = m.add(i, 1)
    i = 0
    while m.lt(i, 8):
        j = m.add(i, 1)
        while m.lt(j, 8):
            si = 1
            while m.le(-1, si):
                sj = 1
                while m.le(-1, sj):
                    parent = m.add(1, m.add(m.mul(2, i), 1 if m.lt(si, 0) else 0))
                    append_composite(curve, qf, entries, parent, j, sj)
                    export_table(report, entries)
                    sj = m.sub(sj, 2)
                si = m.sub(si, 2)
            j = m.add(j, 1)
        i = m.add(i, 1)
    if not m.eq(size(m, entries), 145):
        raise key.Failure("signed table cardinality")
    report["table_pending"] = False
    return jumps, entries, hg


def append_composite(curve, qf, entries, parent_index, i, sign):
    m = curve.m
    parent = m.read(entries, parent_index)
    unit_index = m.add(1, m.add(m.mul(2, i), 1 if m.lt(sign, 0) else 0))
    unit = m.read(entries, unit_index)
    point, h, kind = curve.add_h(parent["point"], parent["h"], unit["point"], unit["h"])
    v = copy_vector(m, parent["vector"])
    m.write(v, i, m.add(m.read(v, i), sign))
    index = rank(m, v)
    if not m.eq(index, size(m, entries)):
        raise ValueError("formal vector ordering mismatch")
    m.append(entries, Record(m, point=point, h=h,
        alpha=qf.add(parent["alpha"], unit["alpha"]), vector=v,
        parent=parent_index, signed_jump=Record(m, index=i, sign=sign)))


def export_table(report, entries):
    # No algebra: expose completed paid record payloads for cap diagnostics.
    row = entries[-1].values
    point = row["point"]
    report["completed_formal_records"].append({"index": len(entries) - 1,
        "point": None if point is None else [point._x, point._y], "h": row["h"],
        "alpha": row["alpha"], "vector": list(row["vector"]),
        "parent": row["parent"], "signed_jump": None if row["signed_jump"] is None else dict(row["signed_jump"].values)})


class Arm:
    def __init__(self, base, key, curve, g, target, owner, jumps, table,
                 hg, raw_starts, hash_params, report):
        self.base, self.key, self.curve = base, key, curve
        self.m, self.f, self.qf = curve.m, curve.f, inverse_field(base, curve.m, curve.q, "Fq")
        self.g, self.target, self.owner = g, target, owner
        self.jumps, self.table, self.hg = jumps, table, hg
        self.phase("setup")
        self.report, self.walkers, self.references = report, [], []
        self.heads, self.dp = [], []
        self.solved, self.round = False, 0
        self.completed, self.hzero = 0, 0
        self.solver_pending = None
        self.hq = None
        report.update(status="initializing", rounds_completed=0, verified_scalar=None,
                      walkers=[], miller=[], pending=None, batches=[], terminal_checks=[],
                      first_output_check_scope="validation includes paid uncommitted overshoot; first_transition_checked additionally requires a completed solver/reference commit",
                      partial_commit_scope="cap with pending.consistent_pair=False retains pending/inconclusive status and is not a terminal pair")
        self.scratch = []
        self.reference_scratch = []
        self.batch_scratch = []
        self.peak_solver_words = 0
        self.peak_reference_words = 0
        self.peak_combined_words = 0
        # Available even if the cap interrupts the first partial allocation.
        report["working_memory_bounds"] = working_memory_bounds(owner)
        self.phase("input_dispatch")
        if dispatch_target(key, curve, g, target, owner, report):
            self.solved = True
            return
        self.phase("setup")
        self.hash_a, self.hash_b = hash_params["a"], hash_params["b"]
        if owner == "candidate":
            self.hq = key.binary_h(curve, target, report["miller"], owner + ":Q")
        self.heads = self.m.zeroes(512)
        # Heads use zero sentinel, DP links are 1-based; no free initialized map.
        i = 0
        while self.m.lt(i, 4):
            self.m.active_walker = i
            self.phase("starts")
            raw = self.m.read(raw_starts, i)
            a, b = self.m.read(raw, 0), self.m.read(raw, 1)
            if owner == "candidate":
                pa, ha = curve.scalar_h(a, g, hg)
                pb, hb = curve.scalar_h(b, target, self.hq)
                point, h, _ = curve.add_h(pa, ha, pb, hb)
            else:
                point, _, _ = curve.add(curve.scalar(a, g), curve.scalar(b, target))
                h = None
            point, h, sign = canonical(curve, point, h)
            self.phase("labels")
            if self.m.eq(sign, -1):
                a, b = self.qf.sub(0, a), self.qf.sub(0, b)
            self.phase("starts")
            if owner == "candidate":
                desc = descriptor(self.m, full=point)
                state = Record(self.m, origin=point, origin_h=h, origin_a=a, origin_b=b,
                               index=0, epsilon=1, depth=0, h=h, a=a, b=b,
                               desc=desc, live=True, ring=[], ring_next=0, transitions=0)
            else:
                state = Record(self.m, point=point, a=a, b=b, live=True,
                               ring=[], ring_next=0, transitions=0)
            self.m.append(self.walkers, state)
            report["walkers"].append({"index": i, "initialized": True,
                "transitions": 0, "termination": None, "first_transition_checked": False,
                "first_output_miller_checked": False, "first_transition_committed": False,
                "start_reference_checked": False})
            self.state_export()
            self.insert_ring(state)
            # Reference points are separately constructed: never share solver output.
            self.phase("reference")
            rp, _, _ = curve.add(curve.scalar(a, g), curve.scalar(b, target))
            rh = key.binary_h(curve, rp, report["miller"], owner + ":start:" + str(i))
            if owner == "candidate" and not self.m.eq(rh, h):
                raise key.Failure("start independent Miller mismatch")
            self.m.append(self.references, Record(self.m, point=rp, h=rh, a=a, b=b))
            self.key.need(curve.equal(rp, point), "start reference/labels mismatch")
            report["walkers"][i]["start_reference_checked"] = True
            self.memory_sample()
            self.state_export()
            self.phase("starts")
            self.m.active_walker = None
            i = self.m.add(i, 1)
        report["status"] = "live"
        report["paid_batch_overshoot_outputs"] = 0

    def phase(self, category):
        if category in ("reference", "terminal_diagnostics", "setup"):
            self.m.active_walker = None
        self.m.phase = self.case_prefix + self.owner + "/" + category if hasattr(self, "case_prefix") else self.owner + "/" + category

    def state_point(self, state, cache=True):
        return (materialize(self.curve, state["desc"], cache, True)
                if self.owner == "candidate" else state["point"])

    def state_x(self, state):
        if self.owner == "candidate":
            return materialize(self.curve, state["desc"], True, False)
        point = state["point"]
        return None if self.m.eq(point, None) else point.x

    def is_identity(self, state):
        if self.owner == "control":
            return self.m.eq(state["point"], None)
        return self.m.eq(state["desc"]["full"], None) and self.m.eq(state["desc"]["slope"], None)

    def insert_ring(self, state):
        self.phase("ring")
        m = self.m
        if self.owner == "candidate":
            entry = Record(m, h=state["h"], x=None, a=state["a"], b=state["b"], desc=state["desc"])
        else:
            entry = Record(m, x=self.state_x(state), a=state["a"], b=state["b"])
        ring = state["ring"]
        if m.lt(size(m, ring), 8):
            m.append(ring, entry)
        else:
            m.write(ring, state["ring_next"], entry)
        state["ring_next"] = m.rem(m.add(state["ring_next"], 1), 8)

    def verify_scalar(self, value, reason, walker):
        self.phase("verification")
        self.key.need(self.curve.equal(self.curve.scalar(value, self.g), self.target),
                      "recovered scalar fails paid verification")
        self.solved = True
        self.report["verified_scalar"] = value
        self.report["stop_reason"] = reason
        self.report["stop_walker"] = walker
        self.report["first_stop_global_events"] = self.m.total
        self.report["first_stop_phase_vectors"] = snapshot(self.m)
        self.report["first_stop_inverse_expansions"] = inverse_snapshot(self.m)
        self.report["first_stop_I_projection"] = projection(self.m)
        return True

    def recover(self, a1, b1, a2, b2, reason, walker):
        self.phase("labels")
        denominator = self.qf.sub(b2, b1)
        if self.m.eq(denominator, 0):
            self.m.tick("null_recovery")
            return False
        value = self.qf.mul(self.qf.sub(a1, a2), self.qf.inverse(denominator))
        return self.verify_scalar(value, reason, walker)

    def detect(self, index, initial=False):
        self.m.active_walker = index
        self.phase("exceptions")
        m, state = self.m, self.m.read(self.walkers, index)
        if self.is_identity(state):
            if not m.eq(state["b"], 0):
                self.phase("labels")
                value = self.qf.mul(self.qf.sub(0, state["a"]), self.qf.inverse(state["b"]))
                self.verify_scalar(value, "identity", index)
            else:
                self.retire(index, "null_identity")
            return
        if not initial:
            self.phase("ring")
            ring, j = state["ring"], 0
            while m.lt(j, size(m, ring)):
                entry = m.read(ring, j)
                screen = True if self.owner == "control" else m.eq(state["h"], entry["h"])
                if screen:
                    self.phase("false_h_screens" if self.owner == "candidate" else "ring")
                    x = self.state_x(state)
                    oldx = materialize(self.curve, entry["desc"], True, False) if self.owner == "candidate" else entry["x"]
                    if m.eq(x, oldx):
                        if not self.recover(state["a"], state["b"], entry["a"], entry["b"], "ring", index):
                            self.retire(index, "null_ring_repeat")
                        return
                    if self.owner == "candidate":
                        m.tick("false_h_match")
                self.phase("ring")
                j = m.add(j, 1)
        self.phase("DP")
        value = state["h"] if self.owner == "candidate" else state["point"].y
        if m.eq(m.rem(value, 4), 0):
            x = self.state_x(state)
            bucket = m.rem(self.f.add(self.f.mul(self.hash_a, x), self.hash_b), 512)
            link = m.read(self.heads, bucket)
            same = False
            while not m.eq(link, 0):
                entry = m.read(self.dp, m.sub(link, 1))
                if m.eq(x, entry["x"]):
                    if self.recover(state["a"], state["b"], entry["a"], entry["b"], "DP", index):
                        return
                    self.phase("DP")
                    if m.eq(state["a"], entry["a"]) and m.eq(state["b"], entry["b"]):
                        same = True
                link = entry["next"]
            if not same:
                m.append(self.dp, Record(m, x=x, a=state["a"], b=state["b"], next=m.read(self.heads, bucket)))
                m.write(self.heads, bucket, size(m, self.dp))
        if not initial and state["live"]:
            self.insert_ring(state)

    def retire(self, index, reason):
        self.phase("retirement_overhead")
        self.m.read(self.walkers, index)["live"] = False
        self.report["walkers"][index]["termination"] = reason
        self.report["walkers"][index]["costs_at_termination"] = snapshot(self.m)
        self.report["walkers"][index]["failed_work_classification"] = "already paid individually attributed work; common batching/sampling remains shared and is not charged again"

    def plan(self, index):
        self.m.active_walker = index
        self.phase("regular_steps")
        m, f, state = self.m, self.f, self.m.read(self.walkers, index)
        if self.owner == "candidate":
            selector = state["h"]
            i = m.rem(selector, 8)
            entry = m.read(self.table, state["index"])
            v = copy_vector(m, entry["vector"])
            m.write(v, i, m.add(m.read(v, i), state["epsilon"]))
            new_index = rank(m, v)
            offset = m.read(self.table, new_index)
            left, right = state["origin"], offset["point"]
            hl, hr = state["origin_h"], offset["h"]
        else:
            left = state["point"]
            i = m.rem(left.y, 32)
            offset = m.read(self.jumps, i)
            right, hl, hr, new_index = offset["point"], None, None, None
        if m.eq(left, None) or m.eq(right, None) or m.eq(left.x, right.x):
            self.phase("exceptions")
            if self.owner == "candidate":
                point, h, kind = self.curve.add_h(left, hl, right, hr)
            else:
                point, _, kind = self.curve.add(left, right)
                h = None
            if self.owner == "control":
                return Record(m, index=index, alpha=offset["alpha"], point=point,
                              left=left, right=right, numerator=None, denominator=None, kind=kind)
            return Record(m, index=index, table_index=new_index, offset=offset, left=left,
                          right=right, hl=hl, hr=hr, point=point, h=h,
                          numerator=None, denominator=None, kind=kind)
        if self.owner == "control":
            return Record(m, index=index, alpha=offset["alpha"], point=None,
                          left=left, right=right, numerator=f.sub(right.y, left.y),
                          denominator=f.sub(right.x, left.x), kind="regular")
        return Record(m, index=index, table_index=new_index, offset=offset, left=left,
                      right=right, hl=hl, hr=hr, point=None, h=None,
                      numerator=f.sub(right.y, left.y), denominator=f.sub(right.x, left.x), kind="regular")

    def finish(self, plan, inverse):
        self.phase("regular_steps")
        m, f = self.m, self.f
        index = plan["index"]
        m.active_walker = index
        original = m.read(self.walkers, index)
        if self.owner == "control":
            return self.finish_control(plan, inverse, original)
        state = Record(m, **{key: original[key] for key in original.values})
        self.phase("regular_steps")
        regular = m.eq(plan["kind"], "regular")
        if regular:
            slope = f.mul(plan["numerator"], inverse)
            left, right = plan["left"], plan["right"]
            if self.owner == "candidate":
                h = f.sub(f.add(plan["hl"], plan["hr"]), slope)
                desc = descriptor(m, origin=left, offset=right, slope=slope)
                if m.eq(h, 0):
                    self.phase("exceptions")
                    point = materialize(self.curve, desc, True, True)
                    point, h, sign = canonical(self.curve, point, h)
                    desc = descriptor(m, full=point)
                    self.hzero = m.add(self.hzero, 1)
                else:
                    negative = f.sub(0, h)
                    sign = -1 if m.lt(negative, h) else 1
                    h = negative if m.eq(sign, -1) else h
                    desc["sign"] = sign
        else:
            self.phase("exceptions")
            point, h, sign = canonical(self.curve, plan["point"], plan["h"])
            desc = descriptor(m, full=point)
            if self.owner == "candidate" and not m.eq(point, None) and m.eq(h, 0):
                self.hzero = m.add(self.hzero, 1)
        self.phase("labels")
        if self.owner == "candidate":
            a = self.qf.add(state["origin_a"], plan["offset"]["alpha"])
            b = state["origin_b"]
        if m.eq(sign, -1):
            a, b = self.qf.sub(0, a), self.qf.sub(0, b)
        self.phase("refresh")
        depth = m.add(state["depth"], 1)
        refresh = m.eq(depth, 2) or not regular
        if self.owner == "candidate" and m.eq(h, 0):
            refresh = True
        if refresh:
            point = materialize(self.curve, desc, True, True)
            state["origin"], state["origin_h"] = point, h
            state["origin_a"], state["origin_b"] = a, b
            state["index"], state["epsilon"], state["depth"] = 0, 1, 0
        else:
            state["index"], state["epsilon"], state["depth"] = plan["table_index"], sign, depth
        state["desc"], state["h"], state["a"], state["b"] = desc, h, a, b
        state["transitions"] = m.add(state["transitions"], 1)
        return state

    def finish_control(self, plan, inverse, original):
        # A full-affine output needs no h, origin, formal index or descriptor.
        m, f = self.m, self.f
        if m.eq(plan["kind"], "regular"):
            slope = f.mul(plan["numerator"], inverse)
            left, right = plan["left"], plan["right"]
            x = f.sub(f.sub(f.square(slope), left.x), right.x)
            y = f.sub(f.mul(slope, f.sub(left.x, x)), left.y)
            point, _, sign = canonical(self.curve, self.curve.point(x, y))
        else:
            self.phase("exceptions")
            point, _, sign = canonical(self.curve, plan["point"])
        self.phase("labels")
        a, b = self.qf.add(original["a"], plan["alpha"]), original["b"]
        if m.eq(sign, -1):
            a, b = self.qf.sub(0, a), self.qf.sub(0, b)
        self.phase("state_output")
        return Record(m, point=point, a=a, b=b, live=original["live"],
                      ring=original["ring"], ring_next=original["ring_next"],
                      transitions=m.add(original["transitions"], 1))

    def validate_output(self, index, state):
        self.phase("reference")
        m, curve = self.m, self.curve
        ref = m.read(self.references, index)
        rp, rh = ref["point"], ref["h"]
        selector = rh if self.owner == "candidate" else rp.y
        i = m.rem(selector, 8 if self.owner == "candidate" else 32)
        jump = m.read(self.jumps, i)
        if self.owner == "candidate":
            rp, rh, _ = curve.add_h(rp, rh, jump["point"], jump["h"])
        else:
            rp, _, _ = curve.add(rp, jump["point"])
            rh = None
        rp, rh, sign = canonical(curve, rp, rh)
        ra, rb = self.qf.add(ref["a"], jump["alpha"]), ref["b"]
        if m.eq(sign, -1):
            ra, rb = self.qf.sub(0, ra), self.qf.sub(0, rb)
        actual = self.state_point(state, False)
        self.key.need(curve.equal(actual, rp), "deferred/full-coordinate successor mismatch")
        self.key.need(m.eq(state["a"], ra) and m.eq(state["b"], rb), "successor label mismatch")
        if self.owner == "candidate":
            self.key.need(m.eq(state["h"], rh), "successor propagated-h mismatch")
        if m.eq(state["transitions"], 1):
            checked = self.key.binary_h(curve, actual, self.report["miller"], self.owner + ":first:" + str(index))
            if self.owner == "candidate":
                self.key.need(m.eq(checked, rh), "first transition Miller mismatch")
            self.report["walkers"][index]["first_output_miller_checked"] = True
        return Record(m, point=rp, h=rh, a=ra, b=rb)

    def scheduler_phase(self):
        self.phase("scheduler")
        self.m.active_walker = None

    def run(self):
        m = self.m
        if self.solved:  # Dispatcher returned before setup; no walkers exist.
            self.report["status"] = "verified_trivial_input"
            self.report["diagnostics_completed"] = True
            self.report["solver_end_vectors"] = snapshot(m)
            self.report["solver_end_I_projection"] = projection(m)
            return
        i = 0
        self.scheduler_phase()
        while m.lt(i, 4) and not self.solved:
            self.detect(i, True)
            self.memory_sample()
            self.state_export()
            self.scheduler_phase()
            i = m.add(i, 1)
        self.scheduler_phase()
        while m.lt(self.round, 32) and not self.solved:
            plans, denominators = [], []
            self.scratch = [plans, denominators]
            i = 0
            self.scheduler_phase()
            while m.lt(i, 4):
                state = m.read(self.walkers, i)
                if state["live"]:
                    self.report["pending"] = {"operation": "plan", "walker": i, "round": self.round}
                    plan = self.plan(i)
                    self.scheduler_phase()
                    m.append(plans, plan)
                    if m.eq(plan["kind"], "regular"):
                        m.append(denominators, plan["denominator"])
                    self.memory_sample()
                self.scheduler_phase()
                i = m.add(i, 1)
            if m.eq(size(m, plans), 0):
                self.report["stop_reason"] = "all_four_terminated"
                break
            self.phase("regular_steps")
            m.active_walker = None
            self.report["pending"] = {"operation": "batch_inverse", "round": self.round,
                                       "regular_denominators": size(m, denominators)}
            inverses = self.batch_inverse(denominators)
            self.report["batches"].append({"round": self.round, "live": size(m, plans),
                                            "regular": size(m, denominators)})
            # Complete the entire arithmetic batch before examining ANY outputs.
            outputs, reference_outputs = [], []
            self.scratch = [plans, denominators, inverses, outputs]
            self.reference_scratch = [reference_outputs]
            j, r = 0, 0
            self.scheduler_phase()
            while m.lt(j, size(m, plans)):
                plan = m.read(plans, j)
                inverse = None
                if m.eq(plan["kind"], "regular"):
                    inverse = m.read(inverses, r)
                    r = m.add(r, 1)
                self.report["pending"] = {"operation": "finish", "walker": plan["index"], "round": self.round}
                output = self.finish(plan, inverse)
                self.scheduler_phase()
                m.append(outputs, output)
                self.memory_sample()
                j = m.add(j, 1)
            # This loop exists only for diagnostics. Its plan/output reads and
            # index arithmetic cannot influence solver scheduling or detection.
            self.phase("reference")
            j = 0
            while m.lt(j, size(m, plans)):
                m.append(reference_outputs, self.validate_output(m.read(plans, j)["index"], m.read(outputs, j)))
                self.memory_sample()
                j = m.add(j, 1)
            j = 0
            self.scheduler_phase()
            while m.lt(j, size(m, plans)) and not self.solved:
                index = m.read(plans, j)["index"]
                self.phase("state_commit")
                m.active_walker = index
                self.report["pending"] = {"operation": "commit_output", "walker": index, "round": self.round,
                                          "walker_written": False, "reference_written": False,
                                          "consistent_pair": False}
                committed = m.read(outputs, j)
                m.write(self.walkers, index, committed)
                self.report["pending"]["walker_written"] = True
                self.state_export()
                # Reference-array maintenance is diagnostic, never solver work.
                self.phase("reference")
                m.write(self.references, index, m.read(reference_outputs, j))
                self.report["pending"].update(reference_written=True, consistent_pair=True)
                if committed.values["transitions"] == 1:
                    w = self.report["walkers"][index]
                    w["first_transition_committed"] = True
                    w["first_transition_checked"] = w["first_output_miller_checked"]
                self.phase("state_commit")
                m.active_walker = index
                self.completed = m.add(self.completed, 1)
                self.report["walkers"][index]["transitions"] = m.read(self.walkers, index)["transitions"]
                self.report["pending"] = {"operation": "detect_committed_output", "walker": index, "round": self.round}
                self.detect(index)
                self.memory_sample()
                self.state_export()
                self.scheduler_phase()
                j = m.add(j, 1)
            self.report["paid_batch_overshoot_outputs"] = m.sub(size(m, plans), j)
            if m.eq(j, size(m, plans)):
                self.round = m.add(self.round, 1)
                self.report["rounds_completed"] = self.round
            self.scratch = []
            self.batch_scratch = []
            self.reference_scratch = []
            # Drop unrooted local batch aliases before the next allocation.
            plans = denominators = inverses = outputs = reference_outputs = []
            plan = output = state = committed = None
            self.report["pending"] = None
            self.scheduler_phase()
        if not self.solved and "stop_reason" not in self.report:
            self.report["stop_reason"] = "32_rounds"
        self.report["solver_end_vectors"] = snapshot(m)
        self.report["solver_end_I_projection"] = projection(m)
        self.report["status"] = "verified_stop" if self.solved else "finite_unsolved"
        # Even at an early successful stop every initialized walker is checked.
        i = 0
        self.phase("terminal_diagnostics")
        while m.lt(i, size(m, self.walkers)):
            state = m.read(self.walkers, i)
            self.report["pending"] = {"operation": "terminal_check", "walker": i}
            point = self.state_point(state, False)
            h = self.key.binary_h(self.curve, point, self.report["miller"], self.owner + ":terminal:" + str(i))
            if self.owner == "candidate":
                self.key.need(m.eq(h, state["h"]), "terminal Miller mismatch")
            expected, _, _ = self.curve.add(self.curve.scalar(state["a"], self.g), self.curve.scalar(state["b"], self.target))
            self.key.need(self.curve.equal(expected, point), "terminal labels mismatch")
            self.report["terminal_checks"].append({"walker": i, "checked": True})
            i = m.add(i, 1)
        self.report["pending"] = None
        self.report["diagnostics_completed"] = True
        self.report["nonidentity_zero_h_outputs"] = self.hzero
        self.report["completed_transitions"] = self.completed
        self.memory_sample()
        self.state_export()

    def batch_inverse(self, values):
        # H028's Montgomery batch algorithm, made observable for live scratch.
        m, f = self.m, self.f
        n = size(m, values)
        if m.eq(n, 0):
            return []
        prefixes = []
        self.batch_scratch = [prefixes]
        first = m.read(values, 0)
        self.key.need(not m.eq(first, 0), "zero batch denominator")
        m.append(prefixes, first)
        i = 1
        while m.lt(i, n):
            value = m.read(values, i)
            self.key.need(not m.eq(value, 0), "zero batch denominator")
            m.append(prefixes, f.mul(m.read(prefixes, m.sub(i, 1)), value))
            self.memory_sample()
            i = m.add(i, 1)
        inv = f.inverse(m.read(prefixes, m.sub(n, 1)))
        result = m.zeroes(n)
        self.batch_scratch = [prefixes, result]
        self.memory_sample()
        i = m.sub(n, 1)
        while m.lt(0, i):
            m.write(result, i, f.mul(inv, m.read(prefixes, m.sub(i, 1))))
            inv = f.mul(inv, m.read(values, i))
            i = m.sub(i, 1)
        m.write(result, 0, inv)
        return result

    def state_export(self):
        # Copy already computed words, with no algebra, cache writes or ticking.
        if self.owner == "control":
            self.report["committed_states"] = [{"a": s.values["a"], "b": s.values["b"],
                "point": raw_point(s.values["point"]), "live": s.values["live"],
                "transitions": s.values["transitions"]} for s in self.walkers]
            return
        self.report["committed_states"] = [{"a": s.values["a"], "b": s.values["b"],
            "h": s.values["h"], "K_index": s.values["index"],
            "epsilon": s.values["epsilon"], "depth": s.values["depth"],
            "live": s.values["live"], "transitions": s.values["transitions"],
            "origin": raw_point(s.values["origin"]),
            "descriptor": {key: raw_point(value) if key in ("full", "origin", "offset") else value
                for key, value in s.values["desc"].values.items()}}
            for s in self.walkers]

    def memory_sample(self):
        # Observational instrumentation: graph identity and payload counts only.
        # Pointers count as words in their parent; every unique referent counts
        # its own payload once. Diagnostic scratch/reference are separate roots.
        roots = [self.walkers, self.jumps, self.table, self.heads, self.dp, self.scratch, self.batch_scratch]
        solver, seen = payload_words(roots)
        reference, _ = payload_words([self.references, self.reference_scratch, self.report["miller"]])
        combined, _ = payload_words(roots + [self.references, self.reference_scratch, self.report["miller"]])
        self.peak_solver_words = max(self.peak_solver_words, solver)
        self.peak_reference_words = max(self.peak_reference_words, reference)
        self.peak_combined_words = max(self.peak_combined_words, combined)
        self.report["memory"] = {"units": "payload words; pointers/flags/labels one word each; each Fp/Fq coordinate one word; not Python bytes",
            "candidate_table_record_words": 6, "formal_vector_words": 8,
            "signed_jump_metadata_words": 2, "jump_record_words": 3 if self.owner == "candidate" else 2,
            "point_words": 2, "ring_record_words": 5 if self.owner == "candidate" else 3,
            "descriptor_words": 9 if self.owner == "candidate" else 0,
            "walker_record_words": 15 if self.owner == "candidate" else 7,
            "plan_record_words": 12 if self.owner == "candidate" else 8, "DP_heads": 512, "DP_record_words": 4,
            "table_occupancy": len(self.table) if self.table is not None else len(self.jumps),
            "DP_records": len(self.dp),
            "ring_occupancy": [len(s.values["ring"]) for s in self.walkers],
            "sampled_solver_payload_words": solver,
            "peak_sampled_solver_payload_words": self.peak_solver_words,
            "peak_sampled_reference_and_trace_words": self.peak_reference_words,
            "peak_sampled_combined_words": self.peak_combined_words,
            "peak_scope": "checkpoints after each initialized start, batch output, reference output and committed detection; pending allocation at cap may exceed last checkpoint",
            "counts_batch_scratch_and_unique_retained_origins": True,
            "upper_bounds": self.report["working_memory_bounds"]}


def working_memory_bounds(owner):
    """Static overcounts for these four starts/32 rounds, including cap partials.

    No Python-byte or exact-peak claim. The largest frozen p,q have <=14 bits.
    Scalars/Miller are iterative (no recursive stack); inverse power has only
    scalar registers and no hidden vector. Temporary points need two words.
    Entries own 6+8+2+2 words plus list slot (rounded to20); jump records plus
    point/list slot need6 candidate/5 control. Eight state slots overcount the
    four originals and four pending outputs, including private eight-entry
    rings and all descriptor referents even when aliased. At most4*(32+1) DP
    records can be inserted. The transient allowance deliberately overcounts
    unrooted partially constructed records/vectors/points, pending array writes,
    plans, batch prefixes/result (each <=4), rank's <=8 two-field records,
    <=14 Miller digits, scalar multiplication and inverse scratch registers.
    Report dictionaries/traces/counter snapshots are a separate retained layer.
    """
    candidate = owner == "candidate"
    components = {
        "formal_table_including_points_vectors_metadata": 145 * 20 if candidate else 0,
        "jump_records_including_points": 8 * 6 if candidate else 32 * 5,
        "original_and_pending_state_slots_with_rings": 8 * (256 if candidate else 64),
        "DP_records_including_array_slots": 4 * 33 * 5,
        "bucket_heads": 512,
        "inputs_sampling_and_array_root_slots": 256,
        "partial_allocation_batch_and_inverse_transient_allowance": 4096 if candidate else 512}
    # <=13 arm Miller traces: Q bootstrap, four starts, four first outputs,
    # four terminal checks. <=14 steps per trace, each <=9 payload words plus
    # list slot;192 words per trace safely includes headers/pending/digits.
    diagnostic = 13 * 192 + 8 * 8 + 512
    return {"solver_working_payload_upper_bound_words": sum(components.values()),
        "solver_components": components,
        "reference_and_arm_trace_upper_bound_words": diagnostic,
        "combined_arm_working_payload_upper_bound_words": sum(components.values()) + diagnostic,
        "scope": "one arm plus its applicable shared table/inputs, during setup or execution, including interrupted allocations; excludes retained experiment reports and counters",
        "reference_bound_scope": "reference originals/pending outputs, <=13 retained arm Miller traces and512 transient words; table bootstrap trace/report exports belong retained experiment reporting",
        "register_scratch": "inverse_field uses imported iterative binary power; <=32 scalar scratch/register words included in transient allowance even though local registers are free in the event ledger",
        "not_measured_heap_or_exact_peak": True}


def dispatch_target(key, curve, g, target, owner, report):
    """Shared callable entry before bootstrap: return whether Q=O was handled."""
    m = curve.m
    m.phase = owner + "/input_dispatch"
    if not m.eq(target, None):
        report["input_dispatch"] = "nonidentity_continue"
        return False
    m.phase = owner + "/verification"
    scalar = 0
    key.need(curve.equal(curve.scalar(scalar, g), target),
             "trivial-input scalar fails paid recovery verification")
    report.update(input_dispatch="identity_target_stop_before_setup",
                  verified_scalar=scalar, verified=True,
                  stop_reason="identity_target", first_stop_global_events=m.total)
    return True


def raw_point(point):
    # Administrative serialization of already paid coordinate words only.
    return None if point is None else [point._x, point._y]


def payload_words(roots):
    seen = set()
    def visit(value):
        if value is None or isinstance(value, (int, float, str, bool)):
            return 0
        ident = id(value)
        if ident in seen:
            return 0
        seen.add(ident)
        if isinstance(value, Record):
            return len(value.values) + sum(visit(v) for v in value.values.values())
        if hasattr(value, "_x") and hasattr(value, "_y"):
            return 2
        if isinstance(value, dict):
            return len(value) + sum(visit(v) for v in value.values())
        if isinstance(value, (list, tuple)):
            return len(value) + sum(visit(v) for v in value)
        return 0
    return sum(visit(root) for root in roots), seen


def snapshot(m):
    # Instrumentation only, not a numerical algorithm or uncharged completion.
    return {phase: dict(row) for phase, row in m.by_phase_kind.items()}


def inverse_snapshot(m):
    return {key: dict(row) for key, row in m.inverse_rows.items()}


def projection(m):
    out = snapshot(m)
    for inv in m.inverse_rows.values():
        row = out.setdefault(inv["phase"], {})
        mk = "scalar_field_mul" if inv["domain"] == "Fq" else "field_mul"
        sk = "scalar_field_square" if inv["domain"] == "Fq" else "field_square"
        row[mk] = row.get(mk, 0) - inv["completed_M"]
        row[sk] = row.get(sk, 0) - inv["completed_S"]
        row["abstract_I_" + inv["domain"]] = inv["completed"]
        row["unfinished_I_" + inv["domain"]] = inv["attempted"] - inv["completed"]
        # Interrupted M/S remain RAW and are not replaced with a completed I.
    return out


def add_vectors(rows):
    out = {}
    for row in rows:
        for kind, count in row.items():
            out[kind] = out.get(kind, 0) + count
    return out


def attributed_sheet(vectors, fixture_index, seed, owner):
    shared = "fixture" + str(fixture_index) + "/"
    case = shared + "seed" + str(seed) + "/"
    categories = {}
    for phase, row in vectors.items():
        if phase.startswith(case + owner + "/"):
            category = phase[len(case + owner + "/"):]
            if category not in ("reference", "terminal_diagnostics"):
                categories[category] = dict(row)
    sampling = [vectors.get(shared + "shared_sampling/jump_stream", {}),
                vectors.get(shared + "shared_sampling/first8", {}),
                vectors.get(shared + "shared_sampling/hash", {})]
    if owner == "control":
        sampling.append(vectors.get(shared + "shared_sampling/remaining24", {}))
    sampling.append(vectors.get(case + "shared_case_sampling/start_labels", {}))
    categories["sampling_setup_attributed"] = add_vectors(sampling)
    categories["curve_table_setup_attributed"] = dict(vectors.get(shared + owner + "/setup", {}))
    return {"operation_vectors": categories, "total_vector": add_vectors(categories.values()),
            "shared_setup_full_per_single_target": True,
            "failed_walk_is_classification_not_additive": True,
            "bootstrap_trace_export_included_conservatively": True,
            "price_scope": "Fp and Fq primitives distinguished; record words/RAM integer events symbolic, no hardware prices"}


def attribution_report(report, m):
    current, projected = snapshot(m), projection(m)
    for fi, fixture in enumerate(report["fixtures"]):
        for case in fixture["cases"]:
            for owner, arm in case["arms"].items():
                stop = arm.get("first_stop_phase_vectors")
                end = arm.get("solver_end_vectors", current)
                prefix = "fixture" + str(fi) + "/seed" + str(case["seed"]) + "/" + owner + "/"
                arm["individual_walker_work_vectors"] = {phase: rows for phase, rows in m.walker_work.items()
                    if phase.startswith(prefix)}
                arm["failed_walk_classification"] = {str(w["index"]): {
                    "reason": w["termination"],
                    "individually_paid_vector": add_vectors(row.get(w["index"], {}) for phase, row in m.walker_work.items()
                        if phase.startswith(prefix) and not phase.endswith(("/reference", "/terminal_diagnostics"))),
                    "shared_batch_work_not_reallocated": True}
                    for w in arm.get("walkers", []) if w.get("termination") is not None}
                arm["actual_or_partial_single_target_expanded"] = attributed_sheet(end, fi, case["seed"], owner)
                if stop is not None:
                    arm["first_verified_stop_single_target_expanded"] = attributed_sheet(stop, fi, case["seed"], owner)
                    arm["first_verified_stop_single_target_I_projection"] = attributed_sheet(arm["first_stop_I_projection"], fi, case["seed"], owner)
                arm["actual_or_partial_single_target_I_projection"] = attributed_sheet(arm.get("solver_end_I_projection", projected), fi, case["seed"], owner)
        complete = len(fixture["cases"]) == 2 and all(c.get("status") == "completed_finite_diagnostic" for c in fixture["cases"])
        if complete:
            shared = "fixture" + str(fi) + "/"
            actual_shared = {phase: row for phase, row in current.items()
                if phase.startswith(shared + "shared_sampling/") or phase in (shared + "candidate/setup", shared + "control/setup")}
            fixture["actual_two_target_shared_setup_vectors"] = actual_shared
            fixture["amortization"] = "these exact measured setup vectors paid once across two completed targets; single-target sheets attribute their applicable vectors in full"


def direct_checks(key, curve, g, report):
    m = curve.m
    m.phase = "direct_dispatch_diagnostics"
    hg = key.binary_h(curve, g, report["miller"], "dispatch:G")
    for name, left, hl, right, hr in (("identity_left", None, 0, g, hg),
            ("identity_right", g, hg, None, 0), ("tangent", g, hg, g, hg),
            ("vertical", g, hg, curve.neg(g), curve.f.sub(0, hg))):
        m.tick("comparison")
        p, h, kind = curve.add_h(left, hl, right, hr)
        key.need(m.eq(kind, name), "direct exceptional dispatch kind mismatch")
        check = key.binary_h(curve, p, report["miller"], "dispatch:" + name)
        key.need(m.eq(h, check), "direct exceptional dispatch h mismatch")
        report["dispatch_checks"].append({"kind": kind, "checked": True,
            "coverage": "H028 support add_h dispatch only; not candidate plan/finish coverage"})


def execute():
    started = time.monotonic()
    report = {"protocol": "H030-C2-v1", "status": "initializing", "fixtures": [],
        "scope": "synthetic correctness/dynamics diagnostic only; verified complete-work improvement NONE",
        "event_cap": EVENT_CAP, "seconds_guard": SECONDS_CAP,
        "support_cap_override": {"H018_EVENT_CAP": EVENT_CAP, "H018_SECONDS_CAP": SECONDS_CAP},
        "record_model": "all implemented point coordinate and Record accesses cost one payload-word transfer; immutable curve parameters/local registers free; Python heap and instrumentation excluded",
        "kernel_credit": "tau=2 ideal unbatched arithmetic ceiling M+S (A credit zero), before detection/setup/dispatch; not complete-work credit",
        "weighted_inequality": "sum_k w_k*C_single_target[k] < sum_k w_k*B_single_target[k]; only matched completed verified stops may be compared",
        "inversion_convention": "expanded M/S vectors OR separate projection with COMPLETED inverse M/S removed; never add I to expanded costs; interrupted inverse raw work retained",
        "working_memory_bounds": {owner: working_memory_bounds(owner) for owner in ("candidate", "control")},
        "pending": "support_loading"}
    m = None
    try:
        report["protocol_sha256"] = hashlib.sha256(PROTOCOL.read_bytes()).hexdigest()
        report["implementation_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        report["support_sha256"] = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in SUPPORT_PATHS}
        sys.dont_write_bytecode = True
        base, key = load_support()
        base.EVENT_CAP, base.SECONDS_CAP = EVENT_CAP, SECONDS_CAP
        class Meter(base.Meter):
            def check_time(self):
                if time.monotonic() - self.started >= SECONDS_CAP:
                    self.cap_hit = "wall_time"
                    raise base.Halt("global 55-second work guard")
            def tick(self, kind, count=1):
                super().tick(kind, count)
                walker = getattr(self, "active_walker", None)
                if walker is not None:
                    row = self.walker_work.setdefault(self.phase, {}).setdefault(walker, {})
                    row[kind] = row.get(kind, 0) + count
            @property
            def phase(self):
                return self._phase
            @phase.setter
            def phase(self, value):
                scope = getattr(self, "scope", "")
                self._phase = value if not scope or value.startswith(scope) else scope + value
        m = Meter()
        m.started = started  # Import/provenance administration shares wall guard.
        m.inverse_rows = {}
        m.walker_work = {}
        m.active_walker = None
        m.check_time()
        report["pending"] = "fixture_processing"

        class Point:
            def __init__(self, x, y):
                m.tick("field_record_write", 2)
                self._x, self._y = x, y
            @property
            def x(self):
                m.tick("field_record_read")
                return self._x
            @property
            def y(self):
                m.tick("field_record_read")
                return self._y

        key.Point = Point  # Deferred support point construction is now charged.

        class Curve(key.Curve):
            def __init__(self, p, a, b, q):
                self.m, self.f = m, inverse_field(base, m, p)
                self.p, self.a, self.b, self.q = p, a, b, q
                self.point = Point

        fi = 0
        m.phase = "experiment_scheduler"
        while m.lt(fi, 4):
            m.active_walker = None
            m.scope = "fixture" + str(fi) + "/"
            m.phase = "fixture_input"
            p, a, b, q, gx, gy = m.read(FIXTURES, fi)
            curve, g = Curve(p, a, b, q), Point(gx, gy)
            fixture = {"fixture": [p, a, b, q, gx, gy], "cases": [], "miller": [],
                       "dispatch_checks": [], "shared_setup": {}, "pending": "certification"}
            report["fixtures"].append(fixture)
            key.certify(base, curve, g, fixture)
            direct_checks(key, curve, g, fixture)
            fixture["identity_targets"] = []
            for owner in ("candidate", "control"):
                identity_report = {}
                handled = dispatch_target(key, curve, g, None, owner, identity_report)
                key.need(handled, "identity target entry dispatcher did not stop")
                fixture["identity_targets"].append({"arm": owner, **identity_report})
            m.phase = "shared_sampling/jump_stream"
            jump_rng = stream(m, p, q, 0, TAGS["jumps"])
            alpha, i = [], 0
            while m.lt(i, 32):
                m.phase = "shared_sampling/first8" if m.lt(i, 8) else "shared_sampling/remaining24"
                m.append(alpha, m.add(1, draw(m, jump_rng, m.sub(q, 1))))
                i = m.add(i, 1)
            m.phase = "shared_sampling/hash"
            hash_rng = stream(m, p, q, 0, TAGS["hash"])
            hash_params = Record(m, a=m.add(1, draw(m, hash_rng, m.sub(p, 1))), b=draw(m, hash_rng, p))
            # Declared actually shared tables are computed once per fixture.
            candidate_setup = {"miller": []}
            control_setup = {"miller": []}
            fixture["shared_setup"] = {"candidate": candidate_setup, "control": control_setup}
            cj, ct, hg = table_setup(base, key, curve, g, alpha, "candidate", candidate_setup)
            bj, _, _ = table_setup(base, key, curve, g, alpha, "control", control_setup)
            fixture["setup_vectors_at_completion"] = snapshot(m)
            m.phase = "experiment_scheduler"
            si = 0
            while m.lt(si, 2):
                m.phase = "harness_input"
                seed = m.read(SEEDS, si)
                case = {"seed": seed, "status": "input_construction", "arms": {}, "pending": None}
                fixture["cases"].append(case)
                m.scope = "fixture" + str(fi) + "/seed" + str(seed) + "/"
                m.phase = "harness_input"
                target_rng = stream(m, p, q, seed, TAGS["targets"])
                secret = m.add(1, draw(m, target_rng, m.sub(q, 1)))
                target = curve.scalar(secret, g)
                # Secret is deliberately not passed or retained in arm/report.
                del secret
                m.phase = "shared_case_sampling/start_labels"
                start_rng = stream(m, p, q, seed, TAGS["starts"])
                raw_starts, i = [], 0
                while m.lt(i, 4):
                    aa = draw(m, start_rng, q)
                    bb = m.add(1, draw(m, start_rng, m.sub(q, 1)))
                    pair = []
                    m.append(pair, aa)
                    m.append(pair, bb)
                    m.append(raw_starts, pair)
                    i = m.add(i, 1)
                case["raw_labels"] = list(raw_starts)
                for owner, jumps, table, gh in (("candidate", cj, ct, hg), ("control", bj, None, None)):
                    case["pending"] = owner
                    arm_report = {}
                    case["arms"][owner] = arm_report
                    # Prefix begins before starts/setup, so each case has its own ledger.
                    prefix = "fixture" + str(fi) + "/seed" + str(seed) + "/"
                    class CaseArm(Arm):
                        case_prefix = prefix
                    arm = CaseArm(base, key, curve, g, target, owner, jumps, table,
                                  gh, raw_starts, hash_params, arm_report)
                    arm.run()
                case["pending"] = None
                case["status"] = "completed_finite_diagnostic"
                case["matched_first_stop_comparison_admissible"] = all(x.get("status") == "verified_stop" and x.get("diagnostics_completed") for x in case["arms"].values())
                m.phase = "experiment_scheduler"
                si = m.add(si, 1)
            m.scope = "fixture" + str(fi) + "/"
            fixture["pending"] = None
            fixture["actually_shared_two_target_setup"] = "completed both targets; table/jump/hash setup computed once, attributed in full to EACH single-target sheet"
            m.phase = "experiment_scheduler"
            fi = m.add(fi, 1)
        report["pending"] = None
        report["status"] = "completed_finite_diagnostic_only"
    except Exception as exc:
        if m is not None and m.cap_hit:
            report["status"] = "inconclusive_cap"
        else:
            report["status"] = "invalid_or_implementation_error"
        report["error"] = type(exc).__name__ + ": " + str(exc)
    if m is not None:
        attribution_report(report, m)
        report["events"], report["cap_hit"] = m.total, m.cap_hit
        report["expanded_phase_vectors"] = snapshot(m)
        report["abstract_I_projection_phase_vectors"] = projection(m)
        report["inverse_expansions"] = m.inverse_rows
        report["event_categories"] = m.by_kind
        report["phase_events"] = m.by_phase
    retained, _ = payload_words([report])
    report["retained_experiment_reporting"] = {
        "final_payload_words_before_encoding": retained,
        "scope": "all retained fixture/case reports, trace exports, snapshots and attribution sheets; separate from per-arm working bounds; instrumentation counters and JSON encoding excluded",
        "peak_bound": "not asserted for reporting/encoding; only per-arm solver and diagnostic work have static transient bounds"}
    report["elapsed_before_encoding_seconds"] = time.monotonic() - started
    payload = json.dumps(report, indent=2, sort_keys=True)
    if time.monotonic() - started >= SECONDS_CAP and report["status"] == "completed_finite_diagnostic_only":
        report["status"] = "inconclusive_reporting_guard"
        payload = json.dumps(report, indent=2, sort_keys=True)
    sys.stdout.write(payload + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute", action="store_true", help="root admission acknowledgement; does not grant admission")
    args = parser.parse_args()
    if not args.execute:
        parser.error("source-review only: root must admit the sole bounded execution")
    execute()


if __name__ == "__main__":
    main()
