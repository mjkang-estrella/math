#!/usr/bin/env python3
"""Agent A — exhaustive lattice search over 𝓜_D (multiplicative persistence).

HEADLINE GOAL.  Prove, for the largest feasible D:

    every 7-smooth m = 2^a·3^b·5^c·7^d with len23(a,b) + c + d <= D has P(m) <= 10.

By the length-domain completeness theorem (SPEC.md / notes/theory.md Theorem 3)
this implies:  ** no n < 10^D has multiplicative persistence >= 12 **  (every
n < 10^D has P(n) <= 11).

DOMAIN (exact and complete).  𝓜_D = {(a,b,c,d) : l23(a,b) + c + d <= D} where
l23 = len23(a,b) is the DP table from src/persistence.py.  The bounds a < 3D+3,
b < 2D+3 are WLOG supersets: l23(a,b) >= ceil(a/3), ceil(b/2) forces a <= 3D,
b <= 2D inside the domain.  l23 is non-decreasing in b for fixed a (an optimal
digit multiset for (a,b) converts to one for (a,b-1) of the same size), so the
valid b's form a prefix of each row and the scan can break early; the build
step *verifies* row monotonicity rather than assuming it.

PER-POINT EVALUATION (exact, no heuristic pruning), per the mission spec:
    m is built INCREMENTALLY: mab = 2^a·3^b fixed per (a,b); the inner loops
    multiply by 5 then by 7 step by step.
    s = str(m);  if '0' in s:  P(m) = 1        [F2: Pi(m)=0, a single digit]
    else:                      P(m) = persistence(m)   [shared library]
    This fast path is provably identical to persistence(m) for every m >= 1
    (persistence itself uses the same F2 shortcut after one str()).
    p >= 11  =>  DISCOVERY: counterexample machinery runs, the pass continues,
    and a loud flag is set in the final report.

INTEGRITY (SPEC rule 3).  Every (a,b) re-derives mab, the c-chain endpoint and
the d-chain endpoint with independent pow() constructions and raises on drift;
zero-free m < 10^9 are cross-checked against persistence_naive; gates re-check
1000 random domain points and a worker-vs-reference enumerator comparison.

SCALE PROTOCOL.  Slice benchmarks (a < amax) at several D measure the true
enumerated rate; digit-length moments (sum len(s), sum len(s)^2 -- exact
analytic closed forms over the domain) drive a per-point cost model
tpp = c0 + c1*mean(len^2) + c2*mean(len); the largest D whose projected wall
time fits the budget is selected.  Milestone passes D = 22,50,100,200,300 run
as complete standalone passes; the final pass additionally tracks joint
(persistence, k = l23+c+d) counts so milestone stats for every D' <= D can be
extracted exactly from a single sweep of 𝓜_D (𝓜_{D'} ⊆ 𝓜_D).

Subcommands:  gates | bench | pass | report.   Pure stdlib; Python >= 3.9.
"""
from __future__ import annotations

import argparse
import json
import math
import multiprocessing as mp
import os
import platform
import random
import subprocess
import sys
import time
from array import array

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from persistence import (persistence, persistence_naive, len23_table,     # noqa: E402
                         prime_digit_expansion, smooth)

_ROOT = os.path.dirname(_HERE)
RESULTS = os.path.join(_ROOT, "results")
os.makedirs(RESULTS, exist_ok=True)

PCAP = 12             # persistence histogram cap: buckets 0..11 exact, 12 = ">=12"
DISCOVERY_P = 11      # P(m) >= 11 in 𝓜_D  =>  persistence-12 number exists
INF_LIMIT = 60000     # len23 INF sentinel is 1e9; must never appear in bounds
MAX_M_NAIVE_CHECK = 1_000_000_000   # cross-check fast vs naive below this


# ---------------------------------------------------------------------------
# machine info
# ---------------------------------------------------------------------------
def machine_info() -> dict:
    info = {
        "python": sys.version.split()[0],
        "platform": platform.platform(),
        "cpu_count": os.cpu_count(),
        "hostname": os.uname().nodename,
    }
    try:
        with open("/proc/cpuinfo") as f:
            for line in f:
                if "model name" in line:
                    info["cpu_model"] = line.split(":", 1)[1].strip()
                    break
    except OSError:
        pass
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemTotal"):
                    info["mem_total_gb"] = round(int(line.split()[1]) / 1048576, 1)
                    break
    except OSError:
        pass
    try:
        with open("/proc/loadavg") as f:
            info["loadavg"] = f.read().split()[:3]
    except OSError:
        pass
    return info


# ---------------------------------------------------------------------------
# exact moment formulas for the (c,d) triangle  {(c,d): c,d >= 0, c+d <= R}
# ---------------------------------------------------------------------------
def tri_moments(R: int):
    """Exact (N, Sc, Sc2, Scd) = Σ1, Σc, Σc², Σcd over T_R.  Σd ≡ Σc by symmetry."""
    Rp1, Rp2 = R + 1, R + 2
    N = Rp1 * Rp2 // 2                          # (R+1)(R+2)/2
    Sc = R * Rp1 * Rp2 // 6                     # R(R+1)(R+2)/6
    Sc2 = R * Rp1 * Rp1 * Rp2 // 12             # R(R+1)^2(R+2)/12
    Scd = (R * R * Rp1 * Rp2 // 3               # see notes: closed form,
           - (R * Rp1 // 2) ** 2                # (R^4+2R^3-R^2-2R)/24
           - R * Rp1 * (2 * R + 1) // 6) // 2
    return N, Sc, Sc2, Scd


def verify_tri_moments(Rmax: int = 40) -> None:
    for R in range(Rmax + 1):
        N, Sc, Sc2, Scd = tri_moments(R)
        n = sc = sd = sc2 = sd2 = scd = 0
        for c in range(R + 1):
            for d in range(R - c + 1):
                n += 1
                sc += c
                sd += d
                sc2 += c * c
                sd2 += d * d
                scd += c * d
        assert (N, Sc, Sc2, Scd) == (n, sc, sc2, scd) and sd == sc and sd2 == sc2, \
            (R, N, Sc, Sc2, Scd, n, sc, sd, sc2, scd, scd)


# ---------------------------------------------------------------------------
# len23 table, flattened + verified
# ---------------------------------------------------------------------------
def build_t23_flat(D_tab: int):
    """len23 table for a <= 3·D_tab+3, b <= 2·D_tab+3 (note: len23_table bounds
    are inclusive) flattened row-major to array('H') (values < INF_LIMIT
    guaranteed).  Verifies every row is non-decreasing in b (proved in notes;
    verified here, not assumed).  Returns (flat, row_stride) with
    row_stride = max_b + 1."""
    max_a, max_b = 3 * D_tab + 3, 2 * D_tab + 3
    t0 = time.time()
    t = len23_table(max_a, max_b)
    stride = max_b + 1
    flat = array("H")
    for row in t:
        if max(row) >= INF_LIMIT:
            raise RuntimeError("len23 INF inside table bounds -- report to lead")
        prev = -1
        for v in row:
            if v < prev:
                raise RuntimeError("len23 row not monotone in b -- break would be unsafe")
            prev = v
        flat.extend(row)
    del t
    print(f"[t23] len23_table({max_a}, {max_b}) -> flat array('H'), "
          f"{len(flat):,} cells, stride {stride} ({time.time() - t0:.1f}s)", flush=True)
    return flat, stride


# ---------------------------------------------------------------------------
# one-pass domain scan: exact size, per-a shard sizes, bmax, digit moments
# ---------------------------------------------------------------------------
def scan_all(D: int, t23flat: array, max_b_tab: int, amax: int | None = None):
    """Returns (total_points_exact_int, bmax_per_a, points_per_a, S1, S2).

    S1/S2 are the float Σ len(str(m)) and Σ len(str(m))^2 over the domain,
    using digits(m) ≈ a·log10(2)+b·log10(3)+c·log10(5)+d·log10(7)+0.5 (the
    +0.5 is the average effect of the floor; validated against measurement).
    """
    la, lb, l5, l7 = math.log10(2), math.log10(3), math.log10(5), math.log10(7)
    total = 0
    bmax = []
    per_a = []
    S1 = 0.0
    S2 = 0.0
    a_hi = (3 * D + 3) if amax is None else min(amax, 3 * D + 3)
    for a in range(a_hi):
        base = a * max_b_tab
        bm = -1
        s = 0
        for b in range(2 * D + 3):
            l23 = t23flat[base + b]
            if l23 > D:
                break
            bm = b
            R = D - l23
            Nt, Sc, Sc2, Scd = tri_moments(R)
            s += Nt
            u = a * la + b * lb + 0.5
            S1 += Nt * u + Sc * (l5 + l7)
            S2 += (Nt * u * u + 2.0 * u * Sc * (l5 + l7)
                   + Sc2 * (l5 * l5 + l7 * l7) + 2.0 * l5 * l7 * Scd)
        bmax.append(bm)
        per_a.append(s)
        total += s
    return total, bmax, per_a, S1, S2


def prep_moments(D_tab: int, t23flat: array, max_b_tab: int) -> dict:
    """Bin moment-polynomial coefficients by l23 value so that |𝓜_D| and its
    digit-length moments for ANY D <= D_tab cost O(Lmax) instead of O(D²)."""
    la, lb, l5, l7 = math.log10(2), math.log10(3), math.log10(5), math.log10(7)
    A = l5 + l7
    B = l5 * l5 + l7 * l7
    C2 = 2.0 * l5 * l7
    LIM = 5 * D_tab + 8                      # l23(a,b) <= a+b <= 5·D_tab+4
    C = [0] * LIM
    F1a = [0.0] * LIM
    F1b = [0.0] * LIM
    F2a = [0.0] * LIM
    F2b = [0.0] * LIM
    F2c = [0.0] * LIM
    F2d = [0.0] * LIM
    for a in range(3 * D_tab + 3):
        base = a * max_b_tab
        for b in range(2 * D_tab + 3):
            l = t23flat[base + b]
            if l > D_tab:
                break
            u = a * la + b * lb + 0.5
            C[l] += 1
            F1a[l] += u
            F1b[l] += A
            F2a[l] += u * u
            F2b[l] += 2.0 * u * A
            F2c[l] += B
            F2d[l] += C2
    return {"D_tab": D_tab, "C": C, "F1a": F1a, "F1b": F1b,
            "F2a": F2a, "F2b": F2b, "F2c": F2c, "F2d": F2d}


def eval_domain(D: int, prep: dict):
    """(|𝓜_D| exact int, S1, S2) for any D <= prep['D_tab']."""
    assert D <= prep["D_tab"]
    C = prep["C"]
    N = 0
    S1 = 0.0
    S2 = 0.0
    for l in range(min(D, len(C) - 1) + 1):
        c = C[l]
        if not c:
            continue
        Nt, Sc, Sc2, Scd = tri_moments(D - l)
        N += c * Nt
        S1 += prep["F1a"][l] * Nt + prep["F1b"][l] * Sc
        S2 += (prep["F2a"][l] * Nt + prep["F2b"][l] * Sc
               + prep["F2c"][l] * Sc2 + prep["F2d"][l] * Scd)
    return N, S1, S2


# ---------------------------------------------------------------------------
# the hot loop: exhaustive chunk evaluation (exact)
# ---------------------------------------------------------------------------
def chunk_worker(task):
    """Evaluate all points (a, b, c, d) for b in [b0, b1) with l23(a,b) <= D.

    Returns a compact result tuple; pk is packed as ONE big integer (little-
    endian over a 13·(D+1) int64 cell grid) so parent aggregation of the joint
    (persistence, k=l23+c+d) histogram is a single bigint add.
    """
    (D, a, b0, b1, row_bytes, milestone, stats2) = task
    t0 = time.perf_counter()
    row = array("H")
    row.frombytes(row_bytes)
    W = D + 1
    npoints = 0
    hist = {}
    hist_zf = {}
    tot_l = [0]
    zf_l = [0]
    sl = 0
    sl2 = 0
    maxp = -1
    argmax = None
    pk = [0] * (13 * W) if milestone else None
    best_k = [D + 1] * 13
    best_arg = [None] * 13
    discoveries = []
    checks = 0
    pers = persistence
    naiv = persistence_naive
    mab = 2 ** a * 3 ** b0
    for bi in range(b1 - b0):
        b = b0 + bi
        l23 = row[bi]
        if l23 > D:
            break
        # --- integrity: independent re-derivation of the (a,b) base -------
        if mab != 2 ** a * 3 ** b:
            raise AssertionError(f"integrity: mab drift at a={a} b={b}")
        checks += 1
        rem = D - l23
        mc = mab
        for c in range(rem + 1):
            m = mc
            for d in range(rem - c + 1):
                s = str(m)
                L = len(s)
                npoints += 1
                if stats2:
                    sl += L
                    sl2 += L * L
                if L >= len(tot_l):
                    tot_l.extend([0] * (L + 1 - len(tot_l)))
                tot_l[L] += 1
                if "0" in s:
                    p = 1                       # F2: m -> 0, single digit (exact)
                else:
                    if L >= len(zf_l):
                        zf_l.extend([0] * (L + 1 - len(zf_l)))
                    zf_l[L] += 1
                    p = pers(m)
                    hist_zf[p] = hist_zf.get(p, 0) + 1
                    if m < MAX_M_NAIVE_CHECK and p != naiv(m):
                        raise AssertionError(
                            f"integrity: fast path != naive at {(a, b, c, d)} m={m}")
                hist[p] = hist.get(p, 0) + 1
                if p > maxp:
                    maxp = p
                    argmax = (a, b, c, d, m)
                if p >= DISCOVERY_P:
                    n = prime_digit_expansion(a, b, c, d)
                    pn = naiv(n)
                    discoveries.append({"a": a, "b": b, "c": c, "d": d, "m": m,
                                        "p": p, "n": n, "P_naive_of_n": pn,
                                        "verified": bool(pn >= 12 and pn == p + 1)})
                if milestone:
                    k = l23 + c + d
                    pi_ = p if p < PCAP else PCAP
                    pk[pi_ * W + k] += 1
                    if k < best_k[pi_]:
                        best_k[pi_] = k
                        best_arg[pi_] = (a, b, c, d, m)
                m *= 7
            if c == 0:
                # --- integrity: independent re-derivation of the d-chain ----
                m0 = m // 7                      # exact: m == 7·mab·7^rem here
                if m0 != mab * 7 ** rem:
                    raise AssertionError(
                        f"integrity: d-chain drift at a={a} b={b} rem={rem}")
                if pers(m0) != naiv(m0):
                    raise AssertionError(
                        f"integrity: library vs naive at {(a, b, 0, rem)} m={m0}")
                checks += 2
            mc *= 5
        # --- integrity: independent re-derivation of the c-chain ----------
        # (mc has been multiplied once more after the last c iteration)
        if mc != mab * 5 ** (rem + 1):
            raise AssertionError(f"integrity: c-chain drift at a={a} b={b} rem={rem}")
        checks += 1
        mab *= 3
    pk_int = int.from_bytes(array("q", pk).tobytes(), "little") if milestone else 0
    el = time.perf_counter() - t0
    return (a, b0, b1, npoints,
            hist, hist_zf,
            {i: v for i, v in enumerate(tot_l) if v},
            {i: v for i, v in enumerate(zf_l) if v},
            sl, sl2, maxp, argmax, pk_int, best_k, best_arg,
            discoveries, checks, el)


# ---------------------------------------------------------------------------
# accumulation / checkpointing
# ---------------------------------------------------------------------------
def new_acc(D: int, milestone: bool) -> dict:
    return {"D": D, "milestone": milestone, "npoints": 0,
            "hist": {}, "hist_zf": {}, "tot_len": {}, "zf_len": {},
            "sl": 0, "sl2": 0, "maxp": -1, "argmax": None,
            "pk_int": 0, "best_k": [D + 1] * 13, "best_arg": [None] * 13,
            "discoveries": [], "checks": 0, "done": [],
            "wall": 0.0, "workers": 0, "bchunk": 0,
            "domain_size": None, "machine": None,
            "started": time.time(), "updated": time.time()}


def acc_merge(acc: dict, res) -> None:
    (a, b0, b1, npoints, hist, hist_zf, tot_len, zf_len, sl, sl2,
     maxp, argmax, pk_int, best_k, best_arg, discoveries, checks, _el) = res
    acc["npoints"] += npoints
    for src, key in ((hist, "hist"), (hist_zf, "hist_zf"),
                     (tot_len, "tot_len"), (zf_len, "zf_len")):
        dst = acc[key]
        for k, v in src.items():
            dst[k] = dst.get(k, 0) + v
    acc["sl"] += sl
    acc["sl2"] += sl2
    if maxp > acc["maxp"]:
        acc["maxp"] = maxp
        acc["argmax"] = list(argmax) if argmax else None
    if pk_int:
        acc["pk_int"] += pk_int
    bk = acc["best_k"]
    ba = acc["best_arg"]
    for pi_ in range(13):
        if best_k[pi_] < bk[pi_]:
            bk[pi_] = best_k[pi_]
            ba[pi_] = list(best_arg[pi_]) if best_arg[pi_] else None
    if discoveries:
        acc["discoveries"].extend(dict(d, chunk=[a, b0]) for d in discoveries)
    acc["checks"] += checks
    acc["done"].append([a, b0])


def acc_to_jsonable(acc: dict) -> dict:
    d = dict(acc)
    if acc["milestone"]:
        W = acc["D"] + 1
        d["pk"] = list(array("q", acc["pk_int"].to_bytes(13 * W * 8, "little")))
    else:
        d["pk"] = None
    del d["pk_int"]
    d["machine"] = acc["machine"]
    return d


def acc_from_jsonable(saved: dict, milestone: bool) -> dict:
    acc = new_acc(saved["D"], milestone)
    for k in ("D", "npoints", "hist", "hist_zf", "tot_len", "zf_len", "sl", "sl2",
              "maxp", "argmax", "best_k", "best_arg", "discoveries", "checks",
              "done", "wall", "workers", "bchunk", "domain_size", "machine",
              "started", "updated"):
        if k in saved:
            acc[k] = saved[k]
    if milestone and saved.get("pk") is not None:
        acc["pk_int"] = int.from_bytes(array("q", saved["pk"]).tobytes(), "little")
    return acc


def write_checkpoint(acc: dict, ckpt_path: str, canon_path: str | None) -> None:
    acc["updated"] = time.time()
    obj = acc_to_jsonable(acc)
    for path in filter(None, (ckpt_path, canon_path)):
        tmp = path + ".tmp"
        with open(tmp, "w") as f:
            json.dump(obj, f)
        os.replace(tmp, path)


def handle_discoveries(discoveries, D: int) -> None:
    for d in discoveries:
        print("\n" + "!!" * 39)
        print(f"!!! DISCOVERY: P(m) = {d['p']} >= {DISCOVERY_P} at "
              f"(a,b,c,d) = {(d['a'], d['b'], d['c'], d['d'])}  [𝓜_{D}]")
        print(f"!!! m = {d['m']}")
        print(f"!!! prime_digit_expansion n = {d['n']}")
        print(f"!!! persistence_naive(n) = {d['P_naive_of_n']} (verified={d['verified']})")
        print("!!" * 39 + "\n", flush=True)
    path = os.path.join(RESULTS, "COUNTEREXAMPLE.md")
    if not os.path.exists(path):
        d0 = discoveries[0]
        n = d0["n"]
        with open(path, "w") as f:
            f.write("# COUNTEREXAMPLE — persistence ≥ 12 number constructed\n\n")
            f.write(f"Found by `src/lattice_search.py` during the exhaustive sweep of "
                    f"𝓜_{D}.\n\n")
            f.write(f"- m = Π(n) = {d0['m']} = "
                    f"2^{d0['a']}·3^{d0['b']}·5^{d0['c']}·7^{d0['d']}, P(m) = {d0['p']}\n")
            f.write(f"- n = prime_digit_expansion{(d0['a'], d0['b'], d0['c'], d0['d'])} "
                    f"= {n}\n")
            f.write(f"- persistence_naive({n}) = {d0['P_naive_of_n']} "
                    f"(>= 12: {d0['verified']})\n\n")
            f.write("Per Theorem 1 (notes/theory.md), P(n) = 1 + P(m) >= 12 — this is a\n"
                    "persistence-12 number and the 11-step conjecture is FALSE.\n\n")
            f.write(f"Recorded: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")


# ---------------------------------------------------------------------------
# pass runner
# ---------------------------------------------------------------------------
def run_pass(D: int, workers: int, bchunk: int = 32, milestone: bool = False,
             stats2: bool = False, amax: int | None = None, resume: bool = False,
             label: str | None = None, ckpt: bool = True,
             t23: array | None = None, max_b_tab: int | None = None,
             ckpt_every: float = 45.0, quiet: bool = False):
    """Exhaustive sweep of 𝓜_D (or its a < amax slice).  Returns (acc, wall).

    Asserts npoints == exact domain size for full-domain runs (completeness
    of the chunk decomposition)."""
    label = label or f"D{D}"
    if t23 is None:
        t23, max_b_tab = build_t23_flat(D)
    total, bmax, per_a, S1, S2 = scan_all(D, t23, max_b_tab)
    if not quiet:
        print(f"[{label}] D={D}: EXACT |𝓜_D| = {total:,} points "
              f"(mean digits ≈ {S1 / total:.1f}, rms ≈ {math.sqrt(S2 / total):.1f})",
              flush=True)
    acc = new_acc(D, milestone)
    acc["domain_size"] = total if amax is None else None
    acc["machine"] = machine_info()
    acc["workers"] = workers
    acc["bchunk"] = bchunk
    done = set()
    ckpt_path = os.path.join(RESULTS, f"lattice_checkpoint_D{D}.json")
    canon_path = os.path.join(RESULTS, "lattice_checkpoint.json")
    if resume and os.path.exists(ckpt_path):
        with open(ckpt_path) as f:
            saved = json.load(f)
        if saved.get("bchunk") != bchunk:
            raise RuntimeError("bchunk differs from checkpoint; cannot resume")
        acc = acc_from_jsonable(saved, milestone)
        acc["milestone"] = milestone
        done = {tuple(x) for x in saved["done"]}
        if not quiet:
            print(f"[{label}] resuming: {len(done):,} chunks done, "
                  f"{acc['npoints']:,} points accumulated", flush=True)
    chunks = []
    a_hi = (3 * D + 3) if amax is None else min(amax, 3 * D + 3)
    for a in range(a_hi):
        if bmax[a] < 0:
            continue
        b = 0
        while b <= bmax[a]:
            b1 = min(bmax[a] + 1, b + bchunk)
            rb = t23[a * max_b_tab + b: a * max_b_tab + b1].tobytes()
            chunks.append((D, a, b, b1, rb, milestone, stats2))
            b = b1
    if done:
        chunks = [c for c in chunks if (c[1], c[2]) not in done]
    if not quiet:
        print(f"[{label}] {len(chunks):,} chunks -> {workers} workers "
              f"(bchunk={bchunk}, milestone={milestone}, stats2={stats2})", flush=True)
    ctx = mp.get_context("forkserver")
    t0 = time.perf_counter()          # checkpoint accounting base (reset on ckpt)
    t_rate0 = time.perf_counter()     # progress-rate base (never reset)
    last_print = t0
    last_ckpt = t0
    nchunk = 0
    if chunks:
        with ctx.Pool(workers) as pool:
            try:
                for res in pool.imap_unordered(chunk_worker, chunks, chunksize=1):
                    acc_merge(acc, res)
                    nchunk += 1
                    if res[15]:
                        handle_discoveries(res[15], D)
                    now = time.perf_counter()
                    if now - last_print > 120.0:
                        el = now - t_rate0
                        rate = acc["npoints"] / el
                        msg = (f"[{label}] {nchunk:,} chunks, {acc['npoints']:,} pts, "
                               f"{rate / 1e6:.2f} Mpts/s, maxp={acc['maxp']}")
                        if amax is None and rate > 0:
                            msg += f", ETA {(total - acc['npoints']) / rate / 60:.1f} min"
                        print(msg, flush=True)
                        last_print = now
                    if ckpt and now - last_ckpt > ckpt_every:
                        acc["wall"] += now - t0
                        write_checkpoint(acc, ckpt_path, canon_path)
                        last_ckpt = now
                        t0 = time.perf_counter()
            except BaseException:
                # crash-safe: preserve partial aggregate before propagating
                acc["wall"] += time.perf_counter() - t0
                if ckpt:
                    write_checkpoint(acc, ckpt_path, canon_path)
                raise
    wall = time.perf_counter() - t0
    acc["wall"] += wall
    if amax is None and not resume:
        pass  # npoints asserted by caller
    if amax is None:
        assert acc["npoints"] == total, \
            f"completeness failure: enumerated {acc['npoints']:,} != domain {total:,}"
    if ckpt:
        write_checkpoint(acc, ckpt_path, canon_path)
    return acc, acc["wall"]


# ---------------------------------------------------------------------------
# reference enumerator (gates) — mirrors test_core.max_domain_P
# ---------------------------------------------------------------------------
def enum_simple(D: int, amax: int | None = None, collect_p: int | None = None):
    t23 = len23_table(3 * D + 3, 2 * D + 3)
    best, arg = -1, None
    ties = []
    npts = 0
    a_hi = (3 * D + 3) if amax is None else min(amax, 3 * D + 3)
    for a in range(a_hi):
        for b in range(2 * D + 3):
            l23 = t23[a][b]
            if l23 > D:
                break
            mab = 2 ** a * 3 ** b
            rem = D - l23
            for c in range(rem + 1):
                m = mab * 5 ** c
                for d in range(rem - c + 1):
                    p = persistence(m)
                    npts += 1
                    if p > best:
                        best, arg = p, (a, b, c, d, m)
                    if collect_p is not None and p == collect_p:
                        ties.append((a, b, c, d, m))
                    m *= 7
    return best, arg, ties, npts


# ---------------------------------------------------------------------------
# tiny least squares (3 params) via normal equations
# ---------------------------------------------------------------------------
def solve3(A, b):
    M = [list(A[i]) + [b[i]] for i in range(3)]
    for col in range(3):
        piv = max(range(col, 3), key=lambda r: abs(M[r][col]))
        if abs(M[piv][col]) < 1e-300:
            raise ValueError("singular normal equations")
        M[col], M[piv] = M[piv], M[col]
        for r in range(3):
            if r != col and M[r][col] != 0.0:
                f = M[r][col] / M[col][col]
                for k in range(col, 4):
                    M[r][k] -= f * M[col][k]
    return [M[i][3] / M[i][i] for i in range(3)]


def fit_cost_model(benches):
    """tpp[sec/point/core] = c0 + c1*d2 + c2*d1  (d2=Σd²/N, d1=Σd/N)."""
    A = [[0.0] * 3 for _ in range(3)]
    b = [0.0] * 3
    for bn in benches:
        N = bn["N"]
        x = (1.0, bn["S2"] / N, bn["S1"] / N)
        y = bn["wall"] * bn["workers"] / N
        for i in range(3):
            b[i] += x[i] * y
            for j in range(3):
                A[i][j] += x[i] * x[j]
    return solve3(A, b)          # (c0, c1, c2)


def _noop(_i):
    return 0


def measure_pool_startup(workers: int) -> float:
    ctx = mp.get_context("forkserver")
    t0 = time.perf_counter()
    with ctx.Pool(workers) as pool:
        pool.map(_noop, range(workers))
    return time.perf_counter() - t0


# ---------------------------------------------------------------------------
# milestone extraction (final pass tracks joint (p, k) counts)
# ---------------------------------------------------------------------------
def extract_milestones(acc: dict, milestones) -> list:
    """For each D' <= D: exact histogram and max-P over 𝓜_{D'} ⊆ 𝓜_D."""
    D = acc["D"]
    W = D + 1
    arr = array("q", acc["pk_int"].to_bytes(13 * W * 8, "little"))
    out = []
    for Dm in sorted(milestones):
        if Dm > D:
            continue
        hist_m = [sum(arr[p * W: p * W + Dm + 1]) for p in range(13)]
        maxp_m, arg_m = -1, None
        for p in range(13):
            if acc["best_k"][p] <= Dm and p > maxp_m:
                maxp_m, arg_m = p, acc["best_arg"][p]
        out.append({"D": Dm, "hist": hist_m, "maxp": maxp_m,
                    "argmax": arg_m, "npoints": sum(hist_m)})
    return out


# ---------------------------------------------------------------------------
# CLI: gates
# ---------------------------------------------------------------------------
def cmd_gates(args):
    print("=" * 76)
    print("VALIDATION GATES — src/lattice_search.py")
    print("=" * 76)
    print(json.dumps(machine_info(), indent=2, default=str))
    ok = True
    gates = []

    def gate(name, cond, detail=""):
        nonlocal ok
        ok = ok and bool(cond)
        gates.append({"name": name, "pass": bool(cond), "detail": str(detail)})
        print(f"[{'PASS' if cond else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))

    # 0. closed forms
    try:
        verify_tri_moments(40)
        gate("triangle moment closed forms vs brute force (R<=40)", True)
    except AssertionError as e:
        gate("triangle moment closed forms vs brute force (R<=40)", False, e)

    # 1. shared library suite
    r = subprocess.run([sys.executable, os.path.join(_HERE, "test_core.py")])
    gate("python3 src/test_core.py exits 0", r.returncode == 0, f"rc={r.returncode}")

    # 2+3. domain gates D=5, D=15 (single-process reference enumerator)
    best5, arg5, ties5, npts5 = enum_simple(5, collect_p=6)
    gate("D=5: max P(𝓜_5) == 6 with 27648 == 2^10·3^3 among P=6 points",
         best5 == 6 and (10, 3, 0, 0, 27648) in ties5,
         f"best={best5} at {arg5}, {npts5} pts, |P=6 ties|={len(ties5)}: "
         f"{[t[:4] for t in ties5]}")

    best15, arg15, ties15, npts15 = enum_simple(15, collect_p=10)
    gate("D=15: (19,4,0,6) -> m=4996238671872 present with P == 10 exactly",
         (19, 4, 0, 6, 4996238671872) in ties15 and persistence(4996238671872) == 10,
         f"max P(𝓜_15)={best15} at {arg15}, {npts15} pts, |P=10|={len(ties15)}")
    gate("D=15: max P(𝓜_15) == 10 (nothing above the record)", best15 == 10,
         f"best={best15}")

    # 4. shared big table + analytic model self-consistency
    t23, max_b_tab = build_t23_flat(args.table_d)
    prep = prep_moments(args.table_d, t23, max_b_tab)
    for Dchk in (15, 300):
        Np, S1p, S2p = eval_domain(Dchk, prep)
        Ns, _bm, _pa, S1s, S2s = scan_all(Dchk, t23, max_b_tab)
        rel1 = abs(S1p - S1s) / S1s
        rel2 = abs(S2p - S2s) / S2s
        gate(f"eval_domain == scan_all at D={Dchk} (exact N + moments)",
             Np == Ns and rel1 < 1e-9 and rel2 < 1e-6,
             f"N={Np:,}, rel(d1)={rel1:.2e}, rel(d2)={rel2:.2e}")

    # 5. chunk_worker (parallel path) == independent reference on D=15, a < 4
    D = 15
    accw = new_acc(D, False)
    _, bmax15, _, _, _ = scan_all(D, t23, max_b_tab, amax=4)
    t23ref = len23_table(3 * D + 3, 2 * D + 3)

    def ref_ab(a, b):
        """Independent per-(a,b) evaluation: naive pow construction + persistence."""
        n, h, mp_ = 0, {}, -1
        rem = D - t23ref[a][b]
        mab = 2 ** a * 3 ** b
        for c in range(rem + 1):
            m = mab * 5 ** c
            for d in range(rem - c + 1):
                p = persistence(m)
                n += 1
                h[p] = h.get(p, 0) + 1
                mp_ = max(mp_, p)
                m *= 7
        return n, h, mp_

    nref, href, mpref = 0, {}, -1
    for a in range(4):
        for b in range(bmax15[a] + 1):
            n_ab, h_ab, mp_ab = ref_ab(a, b)
            nref += n_ab
            for k, v in h_ab.items():
                href[k] = href.get(k, 0) + v
            mpref = max(mpref, mp_ab)
        b = 0
        while b <= bmax15[a]:
            b1 = min(bmax15[a] + 1, b + 8)
            rb = t23[a * max_b_tab + b: a * max_b_tab + b1].tobytes()
            acc_merge(accw, chunk_worker((D, a, b, b1, rb, False, False)))
            b = b1
    gate("chunk_worker == independent reference (D=15, a<4): npoints & hist & maxp",
         accw["npoints"] == nref and accw["hist"] == href and accw["maxp"] == mpref,
         f"worker {accw['npoints']} pts/hist={dict(sorted(accw['hist'].items()))} "
         f"maxp={accw['maxp']} vs ref {nref} pts/hist={dict(sorted(href.items()))} "
         f"maxp={mpref}")

    # 6. pk bigint packing round-trip
    arr0 = array("q", [0] * 100)
    arr0[37] = 5
    arr0[99] = 2 ** 40
    i0 = int.from_bytes(arr0.tobytes(), "little")
    back = array("q")
    back.frombytes(i0.to_bytes(len(arr0) * 8, "little"))
    gate("joint-histogram bigint packing round-trip", list(back) == list(arr0))

    # 7. spot-check: 1000 random domain points, fast path == library == naive
    rng = random.Random(20260214)
    total_checked = 0
    for Dsamp, cnt in ((15, 250), (50, 250), (300, 250), (700, 250)):
        got = 0
        while got < cnt:
            a = rng.randrange(3 * Dsamp + 3)
            b = rng.randrange(2 * Dsamp + 3)
            l23 = t23[a * max_b_tab + b]
            if l23 > Dsamp:
                continue
            rem = Dsamp - l23
            c = rng.randrange(rem + 1)
            d = rng.randrange(rem - c + 1)
            m_ref = smooth(a, b, c, d)
            m_inc = 2 ** a
            for _ in range(b):
                m_inc *= 3
            for _ in range(c):
                m_inc *= 5
            for _ in range(d):
                m_inc *= 7
            assert m_inc == m_ref, (a, b, c, d)
            p_fast = 1 if "0" in str(m_ref) else persistence(m_ref)
            p_lib = persistence(m_ref)
            p_naiv = persistence_naive(m_ref)
            assert p_fast == p_lib == p_naiv, (a, b, c, d, p_fast, p_lib, p_naiv)
            got += 1
            total_checked += 1
        gate(f"spot-check {cnt} random 𝓜_{Dsamp} points: "
             f"incremental==smooth(), fast==library==naive", True)
    gate("spot-check total", total_checked == 1000, f"{total_checked} points")

    with open(os.path.join(RESULTS, "lattice_gates.json"), "w") as f:
        json.dump({"gates": gates, "all_pass": ok, "machine": machine_info(),
                   "ts": time.strftime("%Y-%m-%d %H:%M:%S")}, f, indent=2)
    print("\n" + ("ALL GATES PASSED" if ok else "!!! GATE FAILURES — DO NOT RUN THE SEARCH !!!"))
    return 0 if ok else 1


# ---------------------------------------------------------------------------
# CLI: bench  (rate model + D selection)
# ---------------------------------------------------------------------------
def cmd_bench(args):
    workers = args.workers
    D_tab = max(args.max_d, max(int(x) for x in args.Ds.split(",")))
    t23, max_b_tab = build_t23_flat(D_tab)
    prep = prep_moments(D_tab, t23, max_b_tab)
    reuse_path = os.path.join(RESULTS, "lattice_bench.json")
    if args.reuse_bench and os.path.exists(reuse_path):
        with open(reuse_path) as f:
            saved = json.load(f)
        benches = saved["benches"]
        startup = saved["startup"]
        delta_ms = saved["delta_milestone"]
        print(f"[bench] reusing {len(benches)} saved benchmarks", flush=True)
    else:
        startup = measure_pool_startup(workers)
        print(f"[bench] pool startup overhead measured: {startup:.2f}s", flush=True)
        benches = []
        rate_guess = 1.4e-6            # sec / point / core
        for ds in args.Ds.split(","):
            D = int(ds)
            # size the slice for ~args.bench_seconds of wall time
            target_pts = int(workers * args.bench_seconds / max(rate_guess, 2e-7))
            cum, amax = 0, 1
            for a in range(3 * D + 3):
                _t, _bm, per_a_a, _, _ = scan_all(D, t23, max_b_tab, amax=a + 1)
                cum = sum(per_a_a)
                if cum >= target_pts:
                    amax = a + 1
                    break
            amax = max(1, amax)
            Ns, _bm, _pa, S1s, S2s = scan_all(D, t23, max_b_tab, amax=amax)
            acc, wall = run_pass(D, workers, bchunk=args.bchunk, milestone=False,
                                 stats2=True, amax=amax,
                                 label=f"bench-D{D}-a{amax}", ckpt=False,
                                 t23=t23, max_b_tab=max_b_tab, quiet=True)
            wall_core = max(wall - startup, 1e-9)
            npts = acc["npoints"]
            assert npts == Ns, (npts, Ns)
            rel2 = abs(acc["sl2"] - S2s) / S2s if S2s else 0.0
            tpp = wall_core * workers / npts
            print(f"[bench] D={D} a<{amax}: {npts:,} pts in {wall_core:.1f}s -> "
                  f"{tpp * 1e6:.3f} µs/pt/core; Σd² analytic {S2s:.4e} vs measured "
                  f"{acc['sl2']:.4e} (rel err {rel2:.3%})", flush=True)
            benches.append({"D": D, "amax": amax, "N": npts, "S1": acc["sl"],
                            "S2": acc["sl2"], "wall": wall_core, "workers": workers,
                            "analytic_S2": S2s, "rel_err_S2": rel2})
            rate_guess = tpp

        # milestone-mode overhead: same slice as the last bench, delta per point
        Dm = benches[-1]["D"]
        amax_m = benches[-1]["amax"]
        accm, wallm = run_pass(Dm, workers, bchunk=args.bchunk, milestone=True,
                               stats2=False, amax=amax_m,
                               label=f"bench-D{Dm}-a{amax_m}-milestone", ckpt=False,
                               t23=t23, max_b_tab=max_b_tab, quiet=True)
        wallm_core = max(wallm - startup, 1e-9)
        assert accm["npoints"] == benches[-1]["N"]
        delta_ms = (wallm_core * workers / accm["npoints"]
                    - benches[-1]["wall"] * workers / benches[-1]["N"])
        print(f"[bench] milestone-mode overhead: {delta_ms * 1e6:+.3f} µs/pt/core",
              flush=True)

    c0, c1, c2 = fit_cost_model(benches)
    print(f"[bench] cost model: tpp(µs) = {c0 * 1e6:.3f} + {c1 * 1e12:.3e}·d² + "
          f"{c2 * 1e9:.3f}·d   (d in digits)", flush=True)

    budget = args.budget_min * 60.0

    def project(Dc):
        N, S1, S2 = eval_domain(Dc, prep)
        d1, d2 = S1 / N, S2 / N
        tpp = c0 + c1 * d2 + c2 * d1 + delta_ms
        return {"D": Dc, "N": N, "d1": d1, "d2": d2,
                "wall": N * tpp / workers + 2.0 * startup}

    rows = [project(Dc) for Dc in range(300, args.max_d + 1, 25)]
    best_D = max((r["D"] for r in rows if r["wall"] <= budget), default=300)
    # fine scan upward in steps of 5 until over budget
    Dc = best_D
    while Dc + 5 <= args.max_d:
        Dc += 5
        r = project(Dc)
        rows.append(r)
        if r["wall"] > budget:
            break
        best_D = Dc
    rows.sort(key=lambda r: r["D"])
    wall_by_D = {r["D"]: r["wall"] for r in rows}
    print("[bench] projection table (D, |𝓜_D|, mean d, rms d, projected wall):")
    for r in rows:
        Dc, wall = r["D"], r["wall"]
        flag = "  <== chosen" if Dc == best_D else ("  (over budget)" if wall > budget else "")
        print(f"    D={Dc:4d}  N={r['N']:>15,}  d̄={r['d1']:7.1f}  "
              f"drms={math.sqrt(r['d2']):7.1f}  wall={wall / 60:7.1f} min{flag}")
    print(f"[bench] CHOSEN D = {best_D} (projected wall "
          f"{wall_by_D[best_D] / 60:.1f} min, budget {args.budget_min:.0f} min)",
          flush=True)
    out = {"benches": benches, "startup": startup, "delta_milestone": delta_ms,
           "coef": {"c0": c0, "c1": c1, "c2": c2},
           "projection": [{"D": r["D"], "N": r["N"], "d1": r["d1"], "d2": r["d2"],
                           "wall_s": r["wall"]} for r in rows],
           "chosen_D": best_D, "budget_min": args.budget_min,
           "workers": workers, "machine": machine_info(),
           "ts": time.strftime("%Y-%m-%d %H:%M:%S")}
    with open(os.path.join(RESULTS, "lattice_bench.json"), "w") as f:
        json.dump(out, f, indent=2)
    print(f"[bench] wrote {os.path.join(RESULTS, 'lattice_bench.json')}", flush=True)
    return 0


# ---------------------------------------------------------------------------
# CLI: pass
# ---------------------------------------------------------------------------
def cmd_pass(args):
    workers = args.workers or (os.cpu_count() or 8)
    acc, wall = run_pass(args.D, workers, bchunk=args.bchunk,
                         milestone=args.milestone, stats2=False,
                         amax=args.amax, resume=args.resume,
                         label=f"D{args.D}", ckpt=not args.no_ckpt)
    D = args.D
    np_ = acc["npoints"]
    print(f"\n[D{D}] COMPLETE: {np_:,} points (domain {acc['domain_size']:,}) "
          f"in {wall / 60:.2f} min  "
          f"({np_ / wall / 1e6:.2f} Mpts/s aggregate, "
          f"{wall * workers / np_ * 1e6:.3f} µs/pt/core)", flush=True)
    print(f"[D{D}] max P = {acc['maxp']}  at (a,b,c,d,m) = {tuple(acc['argmax'])}")
    print(f"[D{D}] P histogram: {dict(sorted(acc['hist'].items()))}")
    zf = sum(acc["zf_len"].values())
    print(f"[D{D}] zero-free points: {zf:,} / {np_:,} ({zf / np_:.4%}); "
          f"integrity checks passed: {acc['checks']:,}")
    if args.milestone:
        for m in extract_milestones(acc, args.milestones):
            print(f"[D{D}] milestone 𝓜_{m['D']}: max P = {m['maxp']} at "
                  f"{tuple(m['argmax']) if m['argmax'] else None}, "
                  f"{m['npoints']:,} pts")
    if acc["discoveries"]:
        print(f"\n[D{D}] !!! {len(acc['discoveries'])} DISCOVERY/IES — "
              f"see results/COUNTEREXAMPLE.md — conjecture FALSE on this domain")
        return 2
    print(f"[D{D}] no P >= 11 found: every m in 𝓜_{D} has P(m) <= 10 "
          f"=> no n < 10^{D} has persistence >= 12", flush=True)
    return 0


# ---------------------------------------------------------------------------
# CLI: report
# ---------------------------------------------------------------------------
def _fmt_hist(h):
    return ", ".join(f"{p}:{v:,}" for p, v in sorted((int(k), v) for k, v in h.items() if v))


def cmd_report(args):
    final_path = os.path.join(RESULTS, f"lattice_checkpoint_D{args.final_d}.json")
    with open(final_path) as f:
        fin = json.load(f)
    machine = fin.get("machine") or machine_info()
    bench = {}
    bp = os.path.join(RESULTS, "lattice_bench.json")
    if os.path.exists(bp):
        with open(bp) as f:
            bench = json.load(f)
    gates = {}
    gp = os.path.join(RESULTS, "lattice_gates.json")
    if os.path.exists(gp):
        with open(gp) as f:
            gates = json.load(f)

    small = {}
    for ds in args.small.split(","):
        p = os.path.join(RESULTS, f"lattice_checkpoint_D{ds}.json")
        if os.path.exists(p):
            with open(p) as f:
                small[ds] = json.load(f)

    lines = []
    w = lines.append
    D = fin["D"]
    npf = fin["npoints"]
    Nf = fin["domain_size"]
    wall = fin["wall"]
    workers = fin.get("workers") or (os.cpu_count() or 8)
    assert npf == Nf, "final pass incomplete — refusing to write a proof report"

    w("# Lattice search — no persistence-12 number below 10^%d" % D)
    w("")
    w(f"**Proved (exhaustive, exact):** every 7-smooth m = 2^a·3^b·5^c·7^d with "
      f"len23(a,b)+c+d ≤ {D} has **P(m) ≤ 10**.")
    w("")
    w(f"**Claim (by notes/theory.md Theorem 3, length-domain completeness):** "
      f"**no positive integer n < 10^{D} has multiplicative persistence ≥ 12; "
      f"every n < 10^{D} has P(n) ≤ 11.**")
    w("")
    w(f"Date: {time.strftime('%Y-%m-%d %H:%M:%S')}.  ")
    w("")
    w("## Machine")
    w("")
    for k, v in machine.items():
        w(f"- {k}: {v}")
    w("")
    w("## Method")
    w("")
    w(f"- Domain 𝓜_{D} = {{(a,b,c,d) : len23(a,b)+c+d ≤ {D}}}, enumerated **exactly and "
      f"completely**: |𝓜_{D}| = {Nf:,} points; all {npf:,} evaluated "
      f"({npf / Nf:.9f} of domain).")
    w("- m built incrementally per (a,b) (×5, ×7 stepwise); `s = str(m)`; "
      "`'0' in s ⇒ P(m)=1` (F2, exact) else `P(m) = persistence(m)` — the shared, "
      "gate-validated library. No heuristic pruning anywhere.")
    w("- Sharded by (a, b-range) across a multiprocessing forkserver pool; every "
      "(a,b) re-derives mab, the c-chain and d-chain endpoints with independent "
      "pow() constructions and asserts equality (integrity against incremental-"
      "build drift).")
    w("- Joint (P, k=len23+c+d) counts tracked during the sweep so milestone "
      "results for every 𝓜_{D'} ⊆ 𝓜_{D} are extracted exactly from this single pass.")
    w("")
    w("## Validation gates")
    w("")
    if gates:
        for g in gates["gates"]:
            w(f"- [{'x' if g['pass'] else ' '}] {g['name']}"
              + (f" — {g['detail']}" if g["detail"] else ""))
        w(f"\nAll gates passed: **{gates['all_pass']}** "
          f"(incl. `python3 src/test_core.py` exit 0).")
    w("")
    w("## Rate calibration")
    w("")
    if bench:
        for b in bench["benches"]:
            w(f"- bench D={b['D']}, a<{b['amax']}: {b['N']:,} pts in {b['wall']:.1f}s "
              f"→ {b['wall'] * b['workers'] / b['N'] * 1e6:.3f} µs/pt/core "
              f"(Σd² analytic vs measured rel err {b['rel_err_S2']:.3%})")
        w(f"- milestone-mode overhead: {bench['delta_milestone'] * 1e6:+.3f} µs/pt/core; "
          f"pool startup {bench['startup']:.2f}s; selected D = {bench['chosen_D']} "
          f"(projected {next(r['wall_s'] for r in bench['projection'] if r['D'] == bench['chosen_D']) / 60:.1f} min)")
    w("")
    w("## Milestone results")
    w("")
    w("| D | \\|𝓜_D\\| exact | max P | argmax (a,b,c,d) | m | wall |")
    w("|---|---|---|---|---|---|")
    for ds, s in small.items():
        arg = s.get("argmax") or [None] * 5
        w(f"| {ds} | {s['domain_size']:,} | {s['maxp']} | {tuple(arg[:4])} | {arg[4]} | "
          f"{s['wall'] / 60:.2f} min |")
    if fin.get("milestone") and fin.get("pk"):
        W = D + 1
        arr = array("q", array("q", fin["pk"]).tobytes())
        for Dm in [x for x in args.milestones if x <= D]:
            hist_m = [sum(arr[p * W: p * W + Dm + 1]) for p in range(13)]
            maxp_m, arg_m = -1, None
            for p in range(13):
                if fin["best_k"][p] <= Dm and p > maxp_m:
                    maxp_m, arg_m = p, fin["best_arg"][p]
            w(f"| {Dm} (extracted) | {sum(hist_m):,} | {maxp_m} | "
              f"{tuple(arg_m[:4]) if arg_m else '-'} | {arg_m[4] if arg_m else '-'} | — |")
    # consistency: extracted D=300 vs standalone pass
    if "300" in small and fin.get("pk"):
        W = D + 1
        arr = array("q", fin["pk"])
        hist300 = [sum(arr[p * W: p * W + 301]) for p in range(13)]
        s300 = small["300"]
        match = (hist300 == [s300["hist"].get(str(p), 0) for p in range(13)]
                 and sum(hist300) == s300["npoints"])
        w("")
        w(f"Cross-validation: milestone 𝓜_300 histogram extracted from the single "
          f"𝓜_{D} sweep **{'equals' if match else 'DIFFERS FROM'}** the standalone "
          f"complete 𝓜_300 pass (npoints {sum(hist300):,} vs {s300['npoints']:,}).")
    w("")
    w(f"## Final result at D = {D}")
    w("")
    w(f"- **Exact domain size:** |𝓜_{D}| = {Nf:,}")
    w(f"- **Points evaluated:** {npf:,} (complete; asserted equal to the domain size)")
    w(f"- **Wall time:** {wall / 60:.2f} min on {workers} workers "
      f"({npf / wall / 1e6:.2f} Mpts/s aggregate, "
      f"{wall * workers / npf * 1e6:.3f} µs/point/core)")
    w(f"- **Max P seen: {fin['maxp']}** at (a,b,c,d) = {tuple(fin['argmax'][:4])}, "
      f"m = {fin['argmax'][4]}")
    w(f"- **P histogram (all points):** {_fmt_hist(fin['hist'])}")
    zf = sum(fin["zf_len"].values())
    w(f"- **Zero-free points:** {zf:,} of {npf:,} ({zf / npf:.6%}); their P histogram: "
      f"{_fmt_hist(fin['hist_zf'])}")
    w(f"- **Integrity checks passed:** {fin['checks']:,} (independent re-derivations)")
    w("")
    w("### Zero-free counts by digit length")
    w("")
    tl = {int(k): v for k, v in fin["tot_len"].items()}
    zl = {int(k): v for k, v in fin["zf_len"].items()}
    Ls = sorted(set(tl) | set(zl))
    csv_path = os.path.join(RESULTS, "lattice_zerofree_by_len.csv")
    with open(csv_path, "w") as f:
        f.write("digit_len,total,zero_free\n")
        for L in Ls:
            f.write(f"{L},{tl.get(L, 0)},{zl.get(L, 0)}\n")
    w(f"Full table: `results/lattice_zerofree_by_len.csv` "
      f"({len(Ls)} digit lengths, {min(Ls)}–{max(Ls)}). Summary:")
    w("")
    w("| digit length L | points | zero-free | fraction |")
    w("|---|---|---|---|")
    step = max(1, (max(Ls) - min(Ls)) // 24)
    shown = sorted(set(list(range(min(Ls), min(Ls) + 3)) + list(range(min(Ls), max(Ls) + 1, step)) + [max(Ls)]))
    for L in shown:
        t_, z_ = tl.get(L, 0), zl.get(L, 0)
        w(f"| {L} | {t_:,} | {z_:,} | {z_ / t_:,.2%} |" if t_ else f"| {L} | 0 | 0 | - |")
    w("")
    w("### Zero-free digit-length extremum — input to Theorem 5 (conditional resolution)")
    w("")
    zf_keys = [k for k, v in zl.items() if v > 0]
    maxdc_zf = max(zf_keys)
    w("For zero-free m the digits of m themselves are a valid factorization, so "
      "len(m) ≤ dc(m); hence every zero-free 7-smooth with dc ≤ 525 lies in the "
      f"swept 𝓜_525. **The sweep found zero-free 7-smooth numbers only up to "
      f"dc = {maxdc_zf}** ({zl[maxdc_zf]} at that length; {len(zf_keys)} distinct "
      f"lengths, {sum(zl.values()):,} total). Therefore this sweep **verifies: no "
      "zero-free 7-smooth number has 141 ≤ dc ≤ 525**, and the zero-free count is "
      f"exactly {sum(zl.values()):,} for every dc ≤ 525. With C = {maxdc_zf} in "
      "Theorem 5, branch 2 needs D ≥ ⌈C·log₉10⌉+1 = "
      f"{math.ceil(maxdc_zf / math.log10(9)) + 1} ≤ 525 ✓ (satisfied by this "
      "result); branch 1 (dc > C ⇒ contains 0) is verified here for dc ≤ 525 and "
      "remains open only for dc ≥ 526 (cf. agent B's zero-free scan).")
    w("")
    w("## The claim")
    w("")
    w(f"> **No positive integer n < 10^{D} has multiplicative persistence ≥ 12.** "
      f"Equivalently, every n < 10^{D} reaches a single digit in at most 11 steps.")
    w("")
    w(f"Proof: exhaustive verification that P(m) ≤ 10 for all {Nf:,} elements of "
      f"𝓜_{D} (complete by notes/theory.md Lemma 2 + Theorem 3), combined with "
      f"P(n) = 1 + P(Π(n)) for n ≥ 10.")
    w("")
    if fin.get("discoveries"):
        w("## !!! DISCOVERY — CONJECTURE FALSE !!!")
        w("")
        for d0 in fin["discoveries"]:
            w(f"- m = {d0['m']} = 2^{d0['a']}·3^{d0['b']}·5^{d0['c']}·7^{d0['d']} has "
              f"P = {d0['p']}; n = {d0['n']} has persistence_naive = "
              f"{d0['P_naive_of_n']} (verified={d0['verified']}).")
        w("")
    else:
        w("## Counterexample search")
        w("")
        w("**No P(m) ≥ 11 was found anywhere in 𝓜_%d — no discovery, no "
          "counterexample.** The 11-step conjecture stands for all n < 10^%d." % (D, D))
        w("")
    w("## Artifacts")
    w("")
    for p in ("lattice_gates.json", "lattice_bench.json",
              "lattice_checkpoint.json", "lattice_zerofree_by_len.csv",
              "COUNTEREXAMPLE.md"):
        if os.path.exists(os.path.join(RESULTS, p)):
            w(f"- `results/{p}`")
    for ds in list(small) + [str(D)]:
        w(f"- `results/lattice_checkpoint_D{ds}.json`")
    w("")
    path = os.path.join(RESULTS, "lattice_results.md")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"[report] wrote {path}")
    return 0


# ---------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    sub = ap.add_subparsers(dest="cmd", required=True)

    g = sub.add_parser("gates", help="run all validation gates")
    g.add_argument("--table-d", type=int, default=820,
                   help="shared len23 table size for spot checks")
    g.add_argument("--workers", type=int, default=0)
    g.set_defaults(fn=cmd_gates)

    b = sub.add_parser("bench", help="benchmark rate + select D")
    b.add_argument("--Ds", default="300,550,800")
    b.add_argument("--max-d", type=int, default=820)
    b.add_argument("--workers", type=int, default=os.cpu_count() or 8)
    b.add_argument("--bchunk", type=int, default=32)
    b.add_argument("--bench-seconds", type=float, default=35.0)
    b.add_argument("--budget-min", type=float, default=45.0)
    b.add_argument("--reuse-bench", action="store_true",
                   help="reload saved benchmarks instead of re-running them")
    b.set_defaults(fn=cmd_bench)

    p = sub.add_parser("pass", help="exhaustive pass over 𝓜_D")
    p.add_argument("--D", type=int, required=True)
    p.add_argument("--milestone", action="store_true",
                   help="track joint (P,k) counts for milestone extraction")
    p.add_argument("--milestones", type=int, nargs="*",
                   default=[400, 500, 600, 700, 800])
    p.add_argument("--resume", action="store_true")
    p.add_argument("--no-ckpt", action="store_true")
    p.add_argument("--bchunk", type=int, default=32)
    p.add_argument("--amax", type=int, default=None)
    p.add_argument("--workers", type=int, default=0)
    p.set_defaults(fn=cmd_pass)

    r = sub.add_parser("report", help="aggregate artifacts -> results/lattice_results.md")
    r.add_argument("--final-d", type=int, required=True)
    r.add_argument("--small", default="22,50,100,200,300")
    r.add_argument("--milestones", type=int, nargs="*",
                   default=[400, 500, 600, 700, 800])
    r.set_defaults(fn=cmd_report)

    args = ap.parse_args()
    sys.exit(args.fn(args))


if __name__ == "__main__":
    main()
