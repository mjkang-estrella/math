#!/usr/bin/env python3
"""Reproducible check of the time-translation covariance used in Lemma A.

A prescribed history in H's chronological merger chart (H section 06,
lem:sharp-merger-coordinates) is built from: birth velocities, an ordered
list of dynamic mergers (pair, time, normal), and one free translation per
group.  Redundant contacts are NOT parameters: they are detected as incoming
crossings of the eps-sphere between lines already in one group, and are
applied as elastic (C) scatterings, so they change later velocities.

Claim checked (exact algebra, here verified in floating point):
  shifting every merger time by lam (with lines extended affinely, i.e. no
  birth/end cut-off of segments) shifts every contact time, merger or
  redundant, by exactly lam and leaves every velocity, every redundant
  normal and every merger flux unchanged.

This is an illustration of an algebraic identity, not a proof; the proof is
in analysis.md, Lemma A.  Pure standard library; deterministic seeds.
"""
import math
import random
import sys

EPS = 0.35


def add(a, b): return [a[k] + b[k] for k in range(3)]
def sub(a, b): return [a[k] - b[k] for k in range(3)]
def mul(c, a): return [c * a[k] for k in range(3)]
def dot(a, b): return sum(a[k] * b[k] for k in range(3))
def norm(a): return math.sqrt(dot(a, a))


def unit(rng):
    while True:
        w = [rng.gauss(0, 1) for _ in range(3)]
        n = norm(w)
        if n > 1e-9:
            return mul(1 / n, w)


class Line:
    """Piecewise affine path: list of (t_start, x(t_start), v)."""

    def __init__(self, v):
        self.seg = [(-math.inf, [0.0, 0.0, 0.0], v)]  # x(0)=0; affine for all t

    def at(self, t):
        ts, xs, v = self.seg[0]
        for s in self.seg:
            if s[0] <= t:
                ts, xs, v = s
        if ts == -math.inf:
            return add(xs, mul(t, v)), v  # first segment stored at time 0
        return add(xs, mul(t - ts, v)), v

    def kick(self, t, vnew):
        x, _ = self.at(t)
        self.seg = [s for s in self.seg if s[0] < t] + [(t, x, vnew)]

    def translate(self, d):
        self.seg = [(s[0], add(s[1], d), s[2]) for s in self.seg]


def first_incoming(lines, groups, t0, t1, exclude):
    """Earliest incoming eps-crossing in (t0,t1) between lines of one group."""
    best = None
    for g in groups:
        g = sorted(g)
        for a in range(len(g)):
            for b in range(a + 1, len(g)):
                p, q = g[a], g[b]
                if (p, q) == exclude:
                    continue
                xp, vp = lines[p].at(t0)
                xq, vq = lines[q].at(t0)
                r, u = sub(xq, xp), sub(vq, vp)
                # |r + s u| = eps, s>0, approaching (r+su).u < 0
                A, B, C = dot(u, u), 2 * dot(r, u), dot(r, r) - EPS ** 2
                if A < 1e-14:
                    continue
                disc = B * B - 4 * A * C
                if disc <= 0:
                    continue
                s = (-B - math.sqrt(disc)) / (2 * A)
                if s <= 1e-12 or t0 + s >= t1:
                    continue
                if best is None or t0 + s < best[0]:
                    best = (t0 + s, p, q)
    return best


def scatter(lines, t, p, q, omega):
    _, vp = lines[p].at(t)
    _, vq = lines[q].at(t)
    c = dot(sub(vp, vq), omega)
    lines[p].kick(t, sub(vp, mul(c, omega)))
    lines[q].kick(t, add(vq, mul(c, omega)))
    return c  # incoming flux (v_p - v_q).omega


def build(vel, mergers, t_end):
    """vel: birth velocities; mergers: list of (p, q, time, omega) increasing."""
    n = len(vel)
    lines = [Line(list(v)) for v in vel]
    groups = [{k} for k in range(n)]
    gid = list(range(n))
    events = []
    t_prev, last_pair = mergers[0][2] - 5.0, None  # nothing redundant before first merger
    schedule = [(m[2], m) for m in mergers] + [(t_end, None)]
    for t_next, m in schedule:
        while True:
            hit = first_incoming(lines, [g for g in groups if len(g) > 1],
                                 t_prev, t_next, last_pair)
            if hit is None:
                break
            th, p, q = hit
            xp, _ = lines[p].at(th)
            xq, _ = lines[q].at(th)
            om = mul(1 / EPS, sub(xq, xp))
            flux = scatter(lines, th, p, q, om)
            events.append(("R", p, q, th, tuple(om), flux))
            t_prev, last_pair = th, (min(p, q), max(p, q))
        if m is None:
            break
        p, q, tm, om = m
        gp, gq = gid[p], gid[q]
        assert gp != gq
        xp, _ = lines[p].at(tm)
        xq, _ = lines[q].at(tm)
        d = sub(add(xp, mul(EPS, om)), xq)
        for k in groups[gq]:
            lines[k].translate(d)
        flux = scatter(lines, tm, p, q, om)
        events.append(("M", p, q, tm, tuple(om), flux))
        groups[gp] |= groups[gq]
        for k in groups[gq]:
            gid[k] = gp
        groups[gq] = set()
        t_prev, last_pair = tm, (min(p, q), max(p, q))
    final_v = [lines[k].at(1e7)[1] for k in range(n)]
    return events, final_v


def random_chart(rng, n):
    vel = [[rng.gauss(0, 1) for _ in range(3)] for _ in range(n)]
    gid = list(range(n))
    times = sorted(rng.uniform(0, 1.0) for _ in range(n - 1))
    mergers = []
    for t in times:
        while True:
            p, q = rng.sample(range(n), 2)
            if gid[p] != gid[q]:
                break
        om = unit(rng)
        mergers.append((p, q, t, om))
        old = gid[q]
        gid = [gid[p] if g == old else g for g in gid]
    return vel, mergers


def incoming_ok(vel, mergers):
    ev, _ = build(vel, mergers, 3.0)
    return all(e[5] > 0 for e in ev if e[0] == "M")


def main():
    rng = random.Random(20261014)
    trials, with_red, worst = 0, 0, 0.0
    while trials < 400:
        n = rng.randint(3, 6)
        vel, mergers = random_chart(rng, n)
        if not incoming_ok(vel, mergers):
            continue
        trials += 1
        ev0, fv0 = build(vel, mergers, 3.0)
        if any(e[0] == "R" for e in ev0):
            with_red += 1
        for lam in (0.37, -0.81, 2.5):
            sh = [(p, q, t + lam, om) for (p, q, t, om) in mergers]
            ev1, fv1 = build(vel, sh, 3.0 + lam)
            assert [e[:3] for e in ev0] == [e[:3] for e in ev1], (ev0, ev1)
            for a, b in zip(ev0, ev1):
                worst = max(worst, abs(b[3] - a[3] - lam),
                            max(abs(x - y) for x, y in zip(a[4], b[4])),
                            abs(a[5] - b[5]))
            for a, b in zip(fv0, fv1):
                worst = max(worst, max(abs(x - y) for x, y in zip(a, b)))
    print(f"charts={trials} charts_with_redundant_contacts={with_red}")
    print(f"max |time shift - lam|, normal, flux, velocity discrepancy = {worst:.3e}")
    ok = worst < 1e-8 and with_red > 20
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
