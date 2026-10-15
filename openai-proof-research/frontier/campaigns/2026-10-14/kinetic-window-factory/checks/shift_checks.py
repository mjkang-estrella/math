"""Numerical sanity checks for the time-shift averaging lemma (Lemma W).

Pure standard-library Python (no numpy). These are illustrations of concrete
ingredients, not proofs:

1. Covariance: in the chronological merger chart of H Section 06, shifting
   every merger time by theta (normals and birth velocities fixed, component
   translation moved by -theta * v_rep) shifts every determined redundant
   contact time by exactly theta and leaves all velocities unchanged.
2. Minkowski volume: for the ordered simplex S = {s < t_1 < ... < t_a < s+tau},
   vol(S - [0, Theta] * 1) = vol(S) * (1 + a * Theta / tau).
3. Averaging inequality on a toy chart: the 3-line cycle (1-2 merger, 2-3
   merger, redundant 1-3 contact, all scattering), merger times uniform on one
   slab D, Gaussian velocities, uniform normals.  Lemma W predicts, for every
   window J,
     Leb(D) * P_D(t* in J)  <=  (|J| / Theta) * Leb(D_Theta) * P_{D_Theta}(t* exists).

Run: python3 shift_checks.py  (writes shift_checks.json next to this file)
"""

import json
import math
import os
import random

EPS = 0.35
RNG = random.Random(20261014)


def add(a, b):
    return [a[0] + b[0], a[1] + b[1], a[2] + b[2]]


def sub(a, b):
    return [a[0] - b[0], a[1] - b[1], a[2] - b[2]]


def mul(s, a):
    return [s * a[0], s * a[1], s * a[2]]


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def unit(a):
    n = math.sqrt(dot(a, a))
    return [a[0] / n, a[1] / n, a[2] / n]


def gauss3():
    return [RNG.gauss(0, 1) for _ in range(3)]


def first_incoming_hit(d, u, t0, eps):
    """Smallest t >= t0 with |d + t u| = eps entering the sphere, else None."""
    a = dot(u, u)
    if a == 0:
        return None
    b = 2 * dot(d, u)
    c = dot(d, d) - eps * eps
    disc = b * b - 4 * a * c
    if disc <= 0:
        return None
    t = (-b - math.sqrt(disc)) / (2 * a)  # the entering root of a straight flight
    if t < t0:
        return None
    return t


def build(vel, x_rep, events, eps, theta=0.0):
    """Formal chronological chart construction.

    events: (kind, p, q, t, n, cflag); kind 'M' = merger at time t with
    contact normal n = (x_p - x_q)/eps; kind 'R' = redundant contact whose
    time is determined (first entering hit on the forward ray).
    Returns (event times, final velocities) or None when a merger is not
    incoming or a redundant contact does not exist.
    """
    m = len(vel)
    V = [list(v) for v in vel]
    A = [[0.0, 0.0, 0.0] for _ in range(m)]
    A[0] = sub(x_rep, mul(theta, vel[0]))
    group = list(range(m))
    last = [-math.inf] * m
    times = []
    for kind, p, q, t, n, cflag in events:
        if kind == "M":
            t = t + theta
            assert group[p] != group[q]
            if dot(sub(V[p], V[q]), n) >= 0:
                return None
            xp = add(A[p], mul(t, V[p]))
            delta = sub(sub(xp, mul(eps, n)), add(A[q], mul(t, V[q])))
            gq = group[q]
            for r in range(m):
                if group[r] == gq:
                    A[r] = add(A[r], delta)
                    group[r] = group[p]
            nn = n
        else:
            assert group[p] == group[q]
            d = sub(A[p], A[q])
            u = sub(V[p], V[q])
            t = first_incoming_hit(d, u, max(last[p], last[q]), eps)
            if t is None:
                return None
            nn = unit(add(d, mul(t, u)))
        if cflag:
            xp = add(A[p], mul(t, V[p]))
            xq = add(A[q], mul(t, V[q]))
            g = dot(sub(V[p], V[q]), nn)
            V[p] = sub(V[p], mul(g, nn))
            V[q] = add(V[q], mul(g, nn))
            A[p] = sub(xp, mul(t, V[p]))
            A[q] = sub(xq, mul(t, V[q]))
        last[p] = last[q] = t
        times.append(t)
    return times, V


def check_covariance(trials=400000):
    worst = 0.0
    realized = 0
    mismatch = 0
    for _ in range(trials):
        m = RNG.randint(3, 5)
        vel = [gauss3() for _ in range(m)]
        x_rep = gauss3()
        tm = sorted(RNG.uniform(0, 1) for _ in range(m - 1))
        events = [("M", k, k + 1, tm[k], unit(gauss3()), RNG.random() < 0.5) for k in range(m - 1)]
        events.append(("R", 0, m - 1, None, None, True))
        base = build(vel, x_rep, events, EPS)
        theta = RNG.uniform(-0.7, 0.7)
        shifted = build(vel, x_rep, events, EPS, theta=theta)
        if (base is None) != (shifted is None):
            mismatch += 1
            continue
        if base is None:
            continue
        realized += 1
        err = abs(shifted[0][-1] - base[0][-1] - theta)
        for vb, vs in zip(base[1], shifted[1]):
            err = max(err, max(abs(x - y) for x, y in zip(vb, vs)))
        worst = max(worst, err)
    return {"trials": trials, "realized_redundant_contacts": realized,
            "existence_mismatch_under_shift": mismatch,
            "max_abs_error_time_shift_and_velocities": worst}


def check_minkowski(samples=1000000):
    out = []
    tau = 1.0
    for a in range(1, 6):
        for Theta in (0.25, 1.0):
            hits = 0
            for _ in range(samples):
                t = [RNG.uniform(-Theta, tau) for _ in range(a)]
                if any(t[i + 1] <= t[i] for i in range(a - 1)):
                    continue
                lo = max(-t[0], 0.0)
                hi = min(tau - t[-1], Theta)
                if lo <= hi:
                    hits += 1
            est = hits / samples * (tau + Theta) ** a
            exact = tau ** a / math.factorial(a) * (1 + a * Theta / tau)
            out.append({"a": a, "Theta": Theta, "monte_carlo": est, "formula": exact,
                        "rel_err": abs(est - exact) / exact})
    return out


def check_averaging(samples=150000):
    tau = 1.0
    Theta = tau

    def tstar(t1, t2):
        vel = [gauss3() for _ in range(3)]
        ev = [("M", 0, 1, t1, unit(gauss3()), True),
              ("M", 1, 2, t2, unit(gauss3()), True),
              ("R", 0, 2, None, None, True)]
        b = build(vel, [0.0, 0.0, 0.0], ev, EPS)
        return None if b is None else b[0][-1]

    tsD = []
    for _ in range(samples):
        t1, t2 = sorted((RNG.uniform(0, tau), RNG.uniform(0, tau)))
        tsD.append(tstar(t1, t2))
    exists_DT = 0
    drawn = 0
    while drawn < samples:
        t1, t2 = sorted((RNG.uniform(-Theta, tau), RNG.uniform(-Theta, tau)))
        if max(-t1, 0.0) > min(tau - t2, Theta):
            continue
        drawn += 1
        if tstar(t1, t2) is not None:
            exists_DT += 1
    volD = tau ** 2 / 2
    volDT = volD * (1 + 2 * Theta / tau)
    pDT = exists_DT / samples
    rows = []
    for k in range(11):
        J0 = 0.25 * k
        for width in (0.02, 0.1, 0.4):
            cnt = sum(1 for x in tsD if x is not None and J0 <= x < J0 + width)
            lhs = cnt / samples * volD
            rhs = width / Theta * volDT * pDT
            rows.append({"J": [J0, J0 + width], "lhs_measure": lhs, "rhs_bound": rhs,
                         "ratio": lhs / rhs if rhs > 0 else None})
    return {"samples": samples,
            "redundant_exists_fraction_on_D": sum(x is not None for x in tsD) / samples,
            "redundant_exists_fraction_on_D_Theta": pDT,
            "max_ratio_lhs_over_rhs": max(r["ratio"] for r in rows if r["ratio"] is not None),
            "rows": rows}


if __name__ == "__main__":
    result = {"eps_used_in_toy_charts": EPS,
              "covariance": check_covariance(),
              "minkowski": check_minkowski(),
              "averaging_toy": check_averaging(),
              "status": "numerical illustration only; not a proof"}
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "shift_checks.json"), "w") as fh:
        json.dump(result, fh, indent=1)
    print(json.dumps(result["covariance"], indent=1))
    print(json.dumps([(r["a"], r["Theta"], round(r["rel_err"], 4)) for r in result["minkowski"]]))
    at = result["averaging_toy"]
    print(json.dumps({k: v for k, v in at.items() if k != "rows"}, indent=1))
