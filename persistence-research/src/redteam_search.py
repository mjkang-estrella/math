#!/usr/bin/env python3
"""RED TEAM (subagent C) — adversarial attacks on the 11-step conjecture + bug hunt.

Run:  python3 src/redteam_search.py     (from anywhere; paths resolved from __file__)

Four attacks (see task brief):
  1. INDEPENDENT FRONTIER: all 7-smooth <= 9^22 by min-heap smooth generation
     (seeded at 1; pop smallest, push *2,*3,*5,*7, set-dedupe). P via library,
     top-20 + 2000 random re-verified with persistence_naive. Plus an exact
     independent maxdomain(D) scan to cross-check the lead's / agent A's D=22 milestone.
  2. PREIMAGE ATTACK on the P>=10 frontier: enumerate every (a,b,c,d) with
     len23(a,b)+c+d <= 30, compute Pi(m') = digit_product(2^a 3^b 5^c 7^d),
     hash-lookup against the frontier. Any hit with P(Pi(m')) >= 10 constructs a
     persistence-12 number via prime_digit_expansion -> results/COUNTEREXAMPLE.md.
  3. MONTE CARLO: 2e6 rejection-sampled (a,b,c,d) with DP-length <= 600 (uniform
     box proposal) + 2e5 length-stratified supplement for small-length coverage.
     Full P-histogram, empirical P(digit-length) curve, naive verification of P>=8.
  4. BRUTE SANITY: DP-array scan (test_core.test_brute_1e7 pattern) to 10^8;
     expect max P = 9 first attained at 26888999 (s_10 = 3778888999 > 10^8);
     5000 random samples cross-checked against persistence().

Read-only: src/persistence.py, src/test_core.py, other agents' files.
Writes: results/redteam_results.md (+ redteam_frontier.csv, redteam_preimage_hits.csv,
redteam_mc_curve.csv, and COUNTEREXAMPLE.md only on a hit).
"""
import csv
import glob
import heapq
import os
import random
import re
import subprocess
import sys
import time
from array import array
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from persistence import (digit_product, persistence, persistence_naive, chain,
                         is_7smooth, smooth, prime_digit_expansion,
                         len23_table, len_of_smooth)

RESULTS_DIR = os.path.join(ROOT, "results")
os.makedirs(RESULTS_DIR, exist_ok=True)
MD_PATH = os.path.join(RESULTS_DIR, "redteam_results.md")
FRONTIER_CSV = os.path.join(RESULTS_DIR, "redteam_frontier.csv")
HITS_CSV = os.path.join(RESULTS_DIR, "redteam_preimage_hits.csv")
CURVE_CSV = os.path.join(RESULTS_DIR, "redteam_mc_curve.csv")
COUNTEREX = os.path.join(RESULTS_DIR, "COUNTEREXAMPLE.md")

LIMIT = 9 ** 22                    # attack 1 value domain
RECORD = 277777788888899           # persistence-11 record (NOT 7-smooth)
MIN_P10 = 4996238671872            # expected min 7-smooth with P = 10
MC_MAXA, MC_MAXB, MC_LEN = 1800, 1200, 600
NPROC = 16                         # be polite: other agents share this box

T0 = time.time()
RED_FLAGS = []


def log(*a):
    print(*a, flush=True)


def md(line=""):
    with open(MD_PATH, "a") as f:
        f.write(line + "\n")


def both(line=""):
    log(line)
    md(line)


def redflag(msg):
    RED_FLAGS.append(msg)
    log("!! RED FLAG:", msg)
    md(f"**🔴 RED FLAG:** {msg}")


def check(name, cond, detail=""):
    tag = "PASS" if cond else "FAIL"
    line = f"- `[{tag}]` {name}" + (f"  — {detail}" if detail else "")
    both(line)
    if not cond:
        RED_FLAGS.append(name)


# ---------------------------------------------------------------------------
# independent len23 implementation (flat int16 table) + certificates
# ---------------------------------------------------------------------------

def build_len23_flat(max_a, max_b):
    """Independent DP for len23 (min #digits from {2,3,4,6,8,9} with product 2^a 3^b).
    Same recurrence as the library (it is the math), different implementation and
    storage; cross-validated against the library and by certificates below."""
    INF = 30000
    W = max_b + 1
    flat = array("h", [INF]) * ((max_a + 1) * W)
    flat[0] = 0
    for a in range(max_a + 1):
        base = a * W
        for b in range(max_b + 1):
            if a == 0 and b == 0:
                continue
            best = INF
            if a >= 1 and flat[base - W + b] + 1 < best:
                best = flat[base - W + b] + 1          # digit 2
            if a >= 2 and flat[base - 2 * W + b] + 1 < best:
                best = flat[base - 2 * W + b] + 1      # digit 4
            if a >= 3 and flat[base - 3 * W + b] + 1 < best:
                best = flat[base - 3 * W + b] + 1      # digit 8
            if b >= 1 and flat[base + b - 1] + 1 < best:
                best = flat[base + b - 1] + 1          # digit 3
            if b >= 2 and flat[base + b - 2] + 1 < best:
                best = flat[base + b - 2] + 1          # digit 9
            if a >= 1 and b >= 1 and flat[base - W + b - 1] + 1 < best:
                best = flat[base - W + b - 1] + 1      # digit 6
            flat[base + b] = best
    return flat


DIGIT_VECS = ((1, 0), (2, 0), (3, 0), (0, 1), (0, 2), (1, 1))  # 2,4,8,3,9,6


def cert_check(flat, W, a, b):
    """Certificate that flat[a*W+b] is exactly len23(a,b):
    (i) no smaller than the information bounds ceil(a/3), ceil(b/2), ceil((a+b)/3);
    (ii) constructible: walk back through cells decreasing by 1 and collect digits
    whose product is exactly 2^a 3^b using exactly t digits."""
    t = flat[a * W + b]
    if t < max(-(-a // 3), -(-b // 2), -(-(a + b) // 3)):
        return False
    ra, rb, need, n = a, b, t, 0
    while need > 0:
        for da, db in DIGIT_VECS:
            if ra >= da and rb >= db and flat[(ra - da) * W + (rb - db)] == need - 1:
                ra -= da
                rb -= db
                need -= 1
                n += 1
                break
        else:
            return False
    return ra == 0 and rb == 0 and n == t


def factor7(m):
    a = b = c = d = 0
    while m % 2 == 0:
        m //= 2; a += 1
    while m % 3 == 0:
        m //= 3; b += 1
    while m % 5 == 0:
        m //= 5; c += 1
    while m % 7 == 0:
        m //= 7; d += 1
    assert m == 1, "not 7-smooth"
    return a, b, c, d


# ---------------------------------------------------------------------------
# section 0 — gates
# ---------------------------------------------------------------------------

BUG_REPRO = None
S_COUNT = 0


def section_gates():
    both("## 0. Validation gates")
    t0 = time.time()
    r = subprocess.run([sys.executable, os.path.join(HERE, "test_core.py")],
                       capture_output=True, text=True)
    check("python3 src/test_core.py exits 0", r.returncode == 0,
          f"({time.time() - t0:.1f}s)")
    if r.returncode != 0:
        both("```")
        both(r.stdout[-1500:])
        both(r.stderr[-1500:])
        both("```")

    check("P(277777788888899) == 11 naive and fast",
          persistence_naive(RECORD) == 11 and persistence(RECORD) == 11)
    check("record chain matches literature",
          chain(RECORD) == [277777788888899, 4996238671872, 438939648, 4478976,
                            338688, 27648, 2688, 768, 336, 54, 20, 0])
    check("Pi(68889) == 27648", digit_product(68889) == 27648)
    check("P(27648) == 6 (naive + fast)",
          persistence_naive(27648) == 6 and persistence(27648) == 6)
    check("27648 = 2^10*3^3 lies in 𝓜_5 (witness digits 6,8,8,8,9 → len23(10,3) ≤ 5; "
          "lower bound ⌈(10+3)/3⌉ = 5 ⇒ = 5)",
          2 ** 10 * 3 ** 3 == 27648 and 6 * 8 * 8 * 8 * 9 == 27648
          and len23_table(10, 3)[10][3] == 5)

    global T90, BUG_REPRO
    t0 = time.time()
    T90 = build_len23_flat(90, 60)
    lib = len23_table(90, 60)
    mism = [(a, b) for a in range(91) for b in range(61)
            if T90[a * 61 + b] != lib[a][b]]
    check("independent len23 builder == library on every (a,b) ∈ [0,90]×[0,60]",
          not mism, f"({time.time() - t0:.1f}s, mismatches={mism[:5]})")
    del lib
    rng = random.Random(7)
    cells = [(rng.randrange(91), rng.randrange(61)) for _ in range(200)]
    cells += [(19, 4), (12, 7), (10, 3), (33, 3), (4, 20)]
    bad = [ab for ab in cells if not cert_check(T90, 61, *ab)]
    check("len23 certificates (bounds + constructible witness) on 205 cells",
          not bad, f"bad={bad[:5]}")

    try:
        len_of_smooth(0, 5, 1, 1)
        check("len_of_smooth(0,5,1,1) works", True)
    except TypeError as e:
        BUG_REPRO = f"len_of_smooth(0,5,1,1) raises TypeError: {e}"
        check("len_of_smooth(0,5,1,1) crashes — CONFIRMED BUG (reported, not patched)",
              True, BUG_REPRO)


# ---------------------------------------------------------------------------
# attack 1 — independent frontier
# ---------------------------------------------------------------------------

def gen_7smooth_heap(limit):
    """Spec generator: min-heap, pop smallest, push ×2,×3,×5,×7, set-dedupe.
    Seeded with 1 (the empty product); the spec's 'seed 2,3,5,7' yields the same
    set minus {1}, and P(1)=0 so nothing changes."""
    seen = {1}
    h = [1]
    out = []
    while h:
        x = heapq.heappop(h)
        out.append(x)
        for p in (2, 3, 5, 7):
            y = x * p
            if y <= limit and y not in seen:
                seen.add(y)
                heapq.heappush(h, y)
    out.sort()
    return out


def maxdomain_scan(D):
    """Exact max P over 𝓜_D = {(a,b,c,d): len23(a,b)+c+d ≤ D}, exhaustive.
    Returns (maxP, list of argmax (a,b,c,d,m), #domain points)."""
    t23 = len23_table(3 * D + 3, 2 * D + 3)
    pw5 = [5 ** i for i in range(D + 2)]
    pw7 = [7 ** i for i in range(D + 2)]
    best, arg, pts = -1, [], 0
    for a in range(3 * D + 3):
        for b in range(2 * D + 3):
            l23 = t23[a][b]
            if l23 > D:
                continue
            mab = 2 ** a * 3 ** b
            rem = D - l23
            for c in range(rem + 1):
                mc = mab * pw5[c]
                for d in range(rem - c + 1):
                    pts += 1
                    m = mc * pw7[d]
                    p = persistence(m)
                    if p > best:
                        best, arg = p, [(a, b, c, d, m)]
                    elif p == best:
                        arg.append((a, b, c, d, m))
    return best, arg, pts


# Lead agent's published milestones (results/lead_milestones.md): D -> (maxP, #points)
LEAD = {8: (8, 2025), 10: (9, 4356), 12: (9, 8281), 14: (9, 14400),
        15: (10, 18496), 16: (10, 23409), 18: (10, 36100), 20: (10, 53361),
        22: (10, 76176)}
LEAD_ARGM = {8: {4478976}, 10: {438939648}, 12: {438939648},
             14: {438939648, 231928233984}, 15: {4996238671872},
             16: {4996238671872},
             18: {4996238671872, 937638166841712},
             20: {4996238671872, 937638166841712},
             22: {4996238671872, 937638166841712}}


def scan_for_agent_a():
    """Best-effort scan for agent A's published maxdomain(22) (excluding this report)."""
    hits = []
    paths = [os.path.join(ROOT, "src", "lattice_search.py")]
    paths += sorted(p for p in glob.glob(os.path.join(RESULTS_DIR, "*.md"))
                    if os.path.basename(p) != os.path.basename(MD_PATH))
    for path in paths:
        if not os.path.exists(path):
            continue
        try:
            text = open(path, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        for i, line in enumerate(text.splitlines()):
            if re.search(r"maxdomain", line) and re.search(r"\b22\b", line):
                hits.append(f"{os.path.basename(path)}:{i + 1}: {line.strip()[:160]}")
    return hits


def attack1():
    both("")
    both("## 1. INDEPENDENT FRONTIER — every 7-smooth m ≤ 9²² by min-heap generation "
         "(different algorithm from the lattice searcher)")
    t0 = time.time()
    S = gen_7smooth_heap(LIMIT)
    n = len(S)
    global S_COUNT
    S_COUNT = n
    both(f"- heap generation (seed 1, pop-min, push ×2/×3/×5/×7, set-dedupe): "
         f"**{n:,} numbers** in {time.time() - t0:.1f}s")

    # cross-validate the generator against an independent exponent-tuple enumeration
    t1 = time.time()
    tup = set()
    p2 = [2 ** i for i in range(70)]
    p3 = [3 ** i for i in range(45)]
    p5 = [5 ** i for i in range(31)]   # 5^30 ≈ 9.31e20 ≤ 9^22 ≈ 9.85e20 < 5^31
    p7 = [7 ** i for i in range(25)]
    for a in range(70):
        pa = p2[a]
        if pa > LIMIT:
            break
        for b in range(45):
            mab = pa * p3[b]
            if mab > LIMIT:
                break
            for c in range(31):
                mc = mab * p5[c]
                if mc > LIMIT:
                    break
                for d in range(25):
                    m = mc * p7[d]
                    if m > LIMIT:
                        break
                    tup.add(m)
    check("heap set == independent exponent-tuple enumeration (two different generators)",
          set(S) == tup, f"({time.time() - t1:.1f}s, |tuple set| = {len(tup):,})")

    Ps = [persistence(m) for m in S]
    hist = Counter(Ps)
    pmax = max(Ps)
    att = [m for m, p in zip(S, Ps) if p == pmax]
    both(f"- P-histogram over the domain: {dict(sorted(hist.items()))}")
    both(f"- **max P over 7-smooth ≤ 9²² = {pmax}**, attained at {len(att)} value(s), "
         f"smallest = {min(att)}")
    if pmax >= 11:
        m = min(att)
        a, b, c, d = factor7(m)
        verify_persistence12(a, b, c, d,
                             f"attack 1: 7-smooth {m} has P = {pmax} ≥ 11")
        redflag(f"7-smooth number with P ≥ 11 found in attack 1: {m}")
    check("max P over 7-smooth ≤ 9²² equals 10", pmax == 10,
          "(< 10 impossible: 4996238671872 is in the domain with P = 10)")

    # naive re-verification: top-20 by (P desc, m asc) + 2000 random
    order = sorted(range(n), key=lambda i: (-Ps[i], S[i]))
    bad = [(S[i], Ps[i], persistence_naive(S[i])) for i in order[:20]
           if persistence_naive(S[i]) != Ps[i]]
    check("top-20 by P re-verified with persistence_naive", not bad, f"bad={bad[:3]}")
    rng = random.Random(20260215)
    bad2 = [S[i] for i in rng.sample(range(n), 2000)
            if persistence_naive(S[i]) != Ps[i]]
    check("2000 random domain members re-verified with persistence_naive",
          not bad2, f"bad={bad2[:3]}")

    m10 = min(m for m, p in zip(S, Ps) if p == 10)
    check("min{m : P(m) = 10} == 4996238671872", m10 == MIN_P10, f"got {m10}")
    fa, fb, fc, fd = factor7(MIN_P10)
    check("4996238671872 = 2^19·3^4·7^6 with len = len23(19,4)+6 = 15",
          (fa, fb, fc, fd) == (19, 4, 0, 6) and T90[19 * 61 + 4] + 6 == 15)

    # P ≥ 9 frontier (full list) -> CSV + md
    rows = []
    F10, F9 = set(), set()
    for m, p in zip(S, Ps):
        if p >= 9:
            a, b, c, d = factor7(m)
            ln = T90[a * 61 + b] + c + d
            rows.append((m, a, b, c, d, ln, p))
            if ln <= 22:
                F9.add(m)
                if p >= 10:
                    F10.add(m)
    rows.sort(key=lambda r: (-r[6], r[0]))
    with open(FRONTIER_CSV, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["m", "a", "b", "c", "d", "len_min_digits", "P"])
        w.writerows(rows)
    both(f"- **P ≥ 9 frontier: {len(rows)} members** "
         f"(P=9: {hist.get(9, 0)}, P=10: {hist.get(10, 0)}); len ≤ 22 subset: "
         f"|F9| = {len(F9)}, |F10| = {len(F10)}. Full list → results/redteam_frontier.csv")
    both("")
    both("| m | (a,b,c,d) | len | P |")
    both("|---|---|---|---|")
    for m, a, b, c, d, ln, p in rows[:40]:
        both(f"| {m} | ({a},{b},{c},{d}) | {ln} | {p} |")
    if len(rows) > 40:
        both(f"| … {len(rows) - 40} more | | | | (see CSV) |")
    check("lead's new frontier member 937638166841712 = 2^4·3^20·7^5 found with P = 10",
          any(r[0] == 937638166841712 and r[6] == 10 for r in rows))
    check("lead's 231928233984 = 2^33·3^3 found with P = 9",
          any(r[0] == 231928233984 and r[6] == 9 for r in rows))

    # independent exact maxdomain(D) scan + comparison with published milestones
    both("")
    both("### Independent exhaustive maxdomain(D) scan (𝓜_D = {len23(a,b)+c+d ≤ D})")
    both("")
    both("| D | my max P | my #points | lead max P | lead #points | my argmax m (P = max) |")
    both("|---|---|---|---|---|---|")
    for D in [5, 8, 10, 12, 14, 15, 16, 18, 20, 22]:
        best, arg, pts = maxdomain_scan(D)
        mset = {t[4] for t in arg}
        if best >= 11:  # cannot happen per the value-domain max, but be loud anyway
            t0a = min(arg, key=lambda t: t[4])
            verify_persistence12(t0a[0], t0a[1], t0a[2], t0a[3],
                                 f"maxdomain({D}) scan found P ≥ 11")
            redflag(f"maxdomain({D}) = {best} ≥ 11 — conjecture broken")
        if D in LEAD:
            lb, lp = LEAD[D]
            check(f"my maxdomain({D}) == lead's published {lb}", best == lb, f"mine={best}")
            check(f"my 𝓜_{D} point count == lead's {lp:,}", pts == lp, f"mine={pts:,}")
            check(f"lead's D={D} argmax members all attain my max",
                  LEAD_ARGM[D] <= mset, f"mine={sorted(mset)}")
            both(f"| {D} | {best} | {pts:,} | {lb} | {lp:,} | {sorted(mset)} |")
        else:
            both(f"| {D} | {best} | {pts:,} | — | — | {sorted(mset)} |")
        if D == 5:
            check("maxdomain(5) == 6 with 27648 among attainers (test_core equivalence)",
                  best == 6 and 27648 in mset)
        if D == 22:
            check("**maxdomain(22) == 10 — the D=22 milestone** (𝓜₂₂ ⊆ {m ≤ 9²²}, "
                  "so any published value ≠ 10 means someone's method is buggy)",
                  best == 10)
    both("")
    aa = scan_for_agent_a()
    if aa:
        both("Agent A / published maxdomain(22) mentions found in repo:")
        for h in aa[:10]:
            both(f"- {h}")
    else:
        both("`src/lattice_search.py` (agent A) not yet published at run time; the "
             "comparison above is against the lead's independent milestones "
             "(`results/lead_milestones.md`). **Whatever agent A publishes for "
             "maxdomain(22) must be exactly 10** — my value-domain scan (𝓜₂₂ ⊆ "
             "{7-smooth ≤ 9²²}) and exhaustive 𝓜₂₂ scan both give 10.")
    return S, Ps, F10, F9


# ---------------------------------------------------------------------------
# attack 2 — preimage attack
# ---------------------------------------------------------------------------

def write_counterexample(n, how):
    c = chain(n)
    with open(COUNTEREX, "w") as f:
        f.write("# COUNTEREXAMPLE — persistence ≥ 12 constructed\n\n")
        f.write(f"n = {n}\n\n")
        f.write(f"persistence_naive(n) = {persistence_naive(n)}\n\n")
        f.write(f"chain: {c}\n\n")
        f.write(f"How: {how}\n\n")
        f.write(f"Verified: {time.strftime('%Y-%m-%d %H:%M:%S')} by src/redteam_search.py\n")


def verify_persistence12(a, b, c, d, how):
    """n = prime_digit_expansion(a,b,c,d) must have naive persistence ≥ 12."""
    n = prime_digit_expansion(a, b, c, d)
    assert digit_product(n) == smooth(a, b, c, d)
    pn = persistence_naive(n)
    assert pn >= 12, f"expected ≥ 12, got {pn}"
    write_counterexample(n, how + f" — n = prime_digit_expansion{a,b,c,d}, "
                                f"Π(n) = 2^{a}·3^{b}·5^{c}·7^{d}")
    return n


def attack2(S, Ps, F10, F9):
    both("")
    both("## 2. PREIMAGE ATTACK on the P = 10 frontier")
    both("")
    both("For every 7-smooth m with P(m) ≥ 10 and len(m) ≤ 22 (attack 1), does there "
         "exist a 7-smooth m′ = 2^a·3^b·5^c·7^d with len(m′) = len23(a,b)+c+d ≤ 30 and "
         "Π(m′) = m? Any hit gives n = prime_digit_expansion(a,b,c,d) with "
         "P(n) = 2 + P(m) ≥ 12.")
    t0 = time.time()
    p2 = [2 ** i for i in range(91)]
    p3 = [3 ** i for i in range(61)]
    p5 = [5 ** i for i in range(31)]
    p7 = [7 ** i for i in range(31)]
    n_pts = 0
    depth = Counter()
    hits10 = []   # P(Pi(m')) >= 10  (superset of the F10-set lookup; complete condition)
    hits9 = []    # Pi(m') in F9
    for a in range(91):
        for b in range(61):
            l23 = T90[a * 61 + b]
            if l23 > 30:
                continue
            mab = p2[a] * p3[b]
            rem = 30 - l23
            for c in range(rem + 1):
                mc = mab * p5[c]
                for d in range(rem - c + 1):
                    n_pts += 1
                    mp = mc * p7[d]
                    Pi = digit_product(mp)
                    pPi = persistence(Pi)
                    depth[pPi] += 1
                    if pPi >= 10:
                        hits10.append((a, b, c, d, mp, Pi, pPi, Pi in F10))
                    elif Pi in F9:
                        hits9.append((a, b, c, d, mp, Pi, pPi))
    dt = time.time() - t0
    both(f"- enumerated **{n_pts:,}** exponent tuples with len23(a,b)+c+d ≤ 30 in "
         f"{dt:.1f}s; depth profile of P(Π(m′)) over all m′: "
         f"{dict(sorted(depth.items()))}")
    check("attack-2 self-test: m′ = 4996238671872 = 2^19·3^4·7^6 is enumerated and "
          "Π(m′) = 438939648 lands in the P ≥ 9 frontier",
          any(t[4] == MIN_P10 and t[5] == 438939648 and t[6] == 9 for t in hits9))
    n9 = prime_digit_expansion(19, 4, 0, 6)
    check("end-to-end pipeline test: prime_digit_expansion(19,4,0,6) has naive P = 11",
          persistence_naive(n9) == 11)
    both(f"- **hits with P(Π(m′)) ≥ 10: {len(hits10)}** (expected 0) "
         f"— of which {sum(1 for t in hits10 if t[7])} also satisfy the literal "
         f"len(m) ≤ 22 frontier-set condition")
    both(f"- closest misses — hits against the P ≥ 9 frontier: **{len(hits9)}**")
    if hits10:
        a, b, c, d, mp, Pi, pPi, inF = hits10[0]
        verify_persistence12(a, b, c, d,
                             f"preimage attack: m′ = 2^{a}·3^{b}·5^{c}·7^{d} = {mp}, "
                             f"Π(m′) = {Pi} has P = {pPi} ≥ 10")
        redflag("preimage attack constructed a persistence-12 number — see "
                "results/COUNTEREXAMPLE.md")
    else:
        both("- no preimage of any P ≥ 10 7-smooth exists with len ≤ 30 → **no "
             "persistence-12 number is reachable from the known frontier within "
             "30-digit preimages**")
    if hits9:
        with open(HITS_CSV, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["a", "b", "c", "d", "m_prime", "Pi_m_prime", "P_of_Pi"])
            w.writerows(sorted(hits9, key=lambda t: (-t[6], t[4])))
        both("")
        both("Closest-miss examples (m′ → Π(m′), P(Π(m′))):")
        for a, b, c, d, mp, Pi, pPi in sorted(hits9, key=lambda t: (-t[6], t[4]))[:12]:
            both(f"- 2^{a}·3^{b}·5^{c}·7^{d} = {mp} → Π = {Pi} (P = {pPi})")
        both(f"- full list → results/redteam_preimage_hits.csv")
    return len(hits10)


# ---------------------------------------------------------------------------
# attack 3 — monte carlo
# ---------------------------------------------------------------------------

_G = {}


def _mc_init(flat):
    _G["t"] = flat


def _mc_worker(payload):
    wid, n_plain, n_strat, seed = payload
    rng = random.Random(seed)
    T = _G["t"]
    W = MC_MAXB + 1
    p2 = [2 ** i for i in range(MC_MAXA + 1)]
    p3 = [3 ** i for i in range(MC_MAXB + 1)]
    p5 = [5 ** i for i in range(MC_LEN + 1)]
    p7 = [7 ** i for i in range(MC_LEN + 1)]
    out = []
    proposals = 0

    def rec(a, b, c, d, src):
        m = p2[a] * p3[b] * p5[c] * p7[d]
        p = persistence(m)
        s = str(m)
        return (T[a * W + b] + c + d, len(s), p, src, s if p >= 8 else None)

    got = 0
    while got < n_plain:                       # uniform box proposal, reject len > 600
        proposals += 1
        a = rng.randrange(MC_MAXA + 1)
        b = rng.randrange(MC_MAXB + 1)
        c = rng.randrange(MC_LEN + 1)
        d = rng.randrange(MC_LEN + 1)
        if T[a * W + b] + c + d > MC_LEN:
            continue
        out.append(rec(a, b, c, d, 0))
        got += 1
    got = 0
    while got < n_strat:                       # length-stratified supplement
        proposals += 1
        L = rng.randrange(1, MC_LEN + 1)
        l23t = rng.randrange(0, L + 1)
        while True:
            proposals += 1
            a = rng.randrange(3 * l23t + 1)
            b = rng.randrange(2 * l23t + 1)
            if T[a * W + b] <= l23t:
                break
        rem = L - l23t
        c = rng.randrange(rem + 1)
        d = rng.randrange(rem - c + 1)
        out.append(rec(a, b, c, d, 1))
        got += 1
    return wid, out, proposals


def attack3():
    both("")
    both("## 3. MONTE CARLO — 2,000,000 rejection-sampled (a,b,c,d) with len ≤ 600 "
         "+ 200,000 length-stratified supplement")
    t0 = time.time()
    flat = build_len23_flat(MC_MAXA, MC_MAXB)
    tlib = time.time()
    lib = len23_table(MC_MAXA, MC_MAXB)
    W = MC_MAXB + 1
    mism = sum(1 for a in range(MC_MAXA + 1) for b in range(MC_MAXB + 1)
               if flat[a * W + b] != lib[a][b])
    check("len23 flat == library on the full [0,1800]×[0,1200] table (2,163,001 cells "
          "— the DP the lattice search rests on)",
          mism == 0, f"({time.time() - tlib:.0f}s to build library table)")
    del lib
    rng = random.Random(11)
    cells = [(rng.randrange(MC_MAXA + 1), rng.randrange(MC_MAXB + 1)) for _ in range(60)]
    cells += [(19, 4), (12, 7), (10, 3), (4, 20), (1800, 0), (0, 1200), (900, 600)]
    bad = [ab for ab in cells if not cert_check(flat, W, *ab)]
    check("len23 certificates on 67 cells across the full range", not bad, f"bad={bad[:5]}")
    both(f"- len23 cross-validation: {time.time() - t0:.0f}s")

    t0 = time.time()
    from multiprocessing import Pool
    n_plain, n_strat = 2_000_000, 200_000
    payloads = [(wid,
                 n_plain // NPROC + (1 if wid < n_plain % NPROC else 0),
                 n_strat // NPROC + (1 if wid < n_strat % NPROC else 0),
                 0xC0FFEE + wid)
                for wid in range(NPROC)]
    hist = Counter()
    curve = {}
    high = []
    n_prop = 0
    with Pool(NPROC, initializer=_mc_init, initargs=(flat,)) as pool:
        for wid, batch, prop in pool.imap_unordered(_mc_worker, payloads, chunksize=1):
            n_prop += prop
            for ldp, nd, p, src, s in batch:
                hist[p] += 1
                b = curve.setdefault(nd, [0, 0, 0, 0, -1])  # n, sumP, n_plain, n_strat, maxP
                b[0] += 1
                b[1] += p
                b[2] += src == 0
                b[3] += src == 1
                if p > b[4]:
                    b[4] = p
                if p >= 8:
                    high.append((p, ldp, nd, s))
    dt = time.time() - t0
    pmax = max(hist)
    both(f"- sampled **{sum(hist.values()):,}** points in {dt:.0f}s "
         f"({n_prop:,} proposals, acceptance {sum(hist.values()) / n_prop:.1%}); "
         f"**max P seen = {pmax}**")
    both(f"- **P-histogram (all 2.2M samples):** "
         f"{', '.join(f'P={k}: {v:,}' for k, v in sorted(hist.items()))}")
    if pmax >= 11:
        subs = [h for h in high if h[0] >= 11]
        for p, ldp, nd, s in subs[:5]:
            m = int(s)
            pn = persistence_naive(m)
            check(f"MC sample with P = {p} naive-verified", pn == p, f"m = {s[:60]}…")
        if any(h[0] >= 11 for h in high):
            p, ldp, nd, s = max(high)
            a, b, c, d = factor7(int(s))
            verify_persistence12(a, b, c, d, f"monte carlo: 7-smooth {s} has P ≥ 11")
            redflag("Monte Carlo found a 7-smooth with P ≥ 11 — conjecture broken")
    bad = []
    rng2 = random.Random(99)
    vset = [h for h in high if h[0] >= 9] + rng2.sample(
        [h for h in high if h[0] == 8], min(2000, sum(1 for h in high if h[0] == 8)))
    for p, ldp, nd, s in vset:
        if persistence_naive(int(s)) != p:
            bad.append(s)
    check(f"naive re-verification of all P ≥ 9 MC samples ({sum(1 for h in high if h[0] >= 9)}) "
          f"+ 2000 random P = 8 samples", not bad, f"bad={bad[:3]}")

    # empirical P(digit-length) curve
    with open(CURVE_CSV, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["decimal_digits", "n_samples", "n_plain", "n_strat",
                    "mean_P", "max_P"])
        for nd in sorted(curve):
            b = curve[nd]
            w.writerow([nd, b[0], b[2], b[3], round(b[1] / b[0], 4), b[4]])
    both("")
    both("### Empirical P(digit-length) curve (decimal digit count of m; "
         "full curve → results/redteam_mc_curve.csv)")
    both("")
    both("| digits | n | n_plain | n_strat | mean P | max P |")
    both("|---|---|---|---|---|---|")
    show = list(range(1, 31)) + [35, 40, 50, 60, 80, 100, 150, 200, 300, 400, 500, 600]
    for nd in show:
        if nd in curve:
            b = curve[nd]
            both(f"| {nd} | {b[0]:,} | {b[2]:,} | {b[3]:,} | {b[1] / b[0]:.3f} | {b[4]} |")
    both("")
    both("The zero-wall is visible: m with ≥ ~25 digits almost always contains a 0 "
         "digit, so P(m) = 1. High persistence lives exclusively at short lengths — "
         "which attack 1 and the 𝓜_D scans cover exhaustively.")


# ---------------------------------------------------------------------------
# attack 4 — brute sanity to 1e8
# ---------------------------------------------------------------------------

def mem_available_mb():
    try:
        for line in open("/proc/meminfo"):
            if line.startswith("MemAvailable"):
                return int(line.split()[1]) // 1024
    except OSError:
        pass
    return 1 << 30


def attack4():
    both("")
    both("## 4. BRUTE SANITY — DP-array scan to 10⁸ (test_core.test_brute_1e7 pattern)")
    N = 10 ** 8
    avail = mem_available_mb()
    if avail < 1500:
        redflag(f"only {avail} MB available; skipping the 10⁸ scan (needs ~500 MB)")
        return
    pi = array("i", [0]) * N          # Pi(n) ≤ 9^8 = 43,046,721 < 2^31
    pers = bytearray(N)
    for i in range(10):
        pi[i] = i
    best, argbest = 0, 0
    t0 = time.time()
    for n in range(10, N):
        x = pi[n // 10] * (n % 10)    # Pi(n); pi(n) < n for n ≥ 10 (F3) ⇒ fused pass OK
        pi[n] = x
        p = 1 + pers[x]
        pers[n] = p
        if p > best:
            best, argbest = p, n
    dt = time.time() - t0
    both(f"- scanned [0, 10⁸) in {dt:.0f}s (~{N / dt / 1e6:.1f}M n/s): "
         f"**max P = {best}, first attained at {argbest}**")
    check("max P below 10⁸ == 9, first attained at 26888999 (s₉; s₁₀ = 3778888999 > 10⁸ "
          "so nothing higher can appear)", best == 9 and argbest == 26888999)
    counts = [pers.count(k) for k in range(10)]
    both(f"- P-level counts below 10⁸: {', '.join(f'P={k}: {v:,}' for k, v in enumerate(counts))}")
    rng = random.Random(424242)
    bad = [x for x in rng.sample(range(1, N), 5000) if persistence(x) != pers[x]]
    check("5000 random n < 10⁸: persistence() == DP value (cross-validates the F2 "
          "zero-shortcut against the shortcut-free DP at scale)", not bad,
          f"bad={bad[:3]}")
    check("record anchors in DP: P(26888999) = 9, P(2677889) = 8, Π(26888999) = 4478976",
          persistence_naive(26888999) == 9 and persistence_naive(2677889) == 8
          and chain(26888999)[1] == 4478976)
    del pi, pers


# ---------------------------------------------------------------------------
# bug report + verdict
# ---------------------------------------------------------------------------

def bug_report():
    both("")
    both("## Bug reports (persistence.py is read-only — reported, not patched)")
    both("")
    both("### BUG C-1: `len_of_smooth` crashes when exactly one of a, b is 0")
    both("")
    both(f"Repro: `{BUG_REPRO}`. Root cause: the default-argument expression "
         "`len23_table(a, b) if a and b else ([[0]] if a == 0 and b == 0 else None)` "
         "evaluates to `None` when a == 0 XOR b == 0 (e.g. m = 3⁵·5·7 or m = 2⁵·7), "
         "and the function then subscripts `None`. Severity: crash (not silent wrong "
         "math), but it fires on the a = 0 and b = 0 axes of the lattice — exactly "
         "where an exhaustive 𝓜_D searcher walks. Workaround used here: index "
         "`len23_table` directly (len = c + d + t23[a][b]). Suggested fix for the lead:")
    both("```python")
    both("if t23 is None:")
    both("    t23 = len23_table(a, b)  # the table itself handles a==0 or b==0 correctly")
    both("```")
    both("")
    both("### Spec errata (no action needed, recorded for the record)")
    both("")
    both("- The brief says the 7-smooth heap domain contains \"~10^4 numbers\"; the "
         f"actual count of 7-smooth ≤ 9²² is {S_COUNT:,} (§1). No consequence.")
    both("- The brief says 277777788888899 is \"> 9²²\"; in fact 277777788888899 ≈ "
         "2.78×10¹⁴ < 9²² ≈ 9.85×10²⁰. It is absent from the heap set because it is "
         "**not 7-smooth** (that is exactly why it can carry P = 11 while every "
         "7-smooth ≤ 9²² has P ≤ 10). Tested separately as required.")


def verdict():
    both("")
    both("## Verdict")
    both("")
    if RED_FLAGS:
        both(f"**{len(RED_FLAGS)} red flag(s):**")
        for r in RED_FLAGS:
            both(f"- {r}")
    else:
        both("**CONJECTURE SURVIVES all four attacks.** No 7-smooth ≤ 9²² has "
             "P ≥ 11 (max = 10, first at 4996238671872); no 30-digit preimage of any "
             "P ≥ 10 frontier member exists (0 hits vs 0 expected, closest misses are "
             "the known P = 9 family); 2.2M Monte Carlo samples up to 600-digit m "
             "never exceeded the known frontier; the 10⁸ DP scan confirms max P = 9 "
             "below 10⁸ with s₁₀ = 3778888999 safely above. One real bug found "
             "(len_of_smooth axes crash) plus two spec errata — see above.")
    both("")
    both(f"*Run completed in {time.time() - T0:.0f}s; redteam_search.py by subagent C.*")


def main():
    with open(MD_PATH, "w") as f:
        f.write(f"# RED TEAM results — subagent C (adversarial attacks + bug hunt)\n\n")
        f.write(f"Run: {time.strftime('%Y-%m-%d %H:%M:%S')} · Python {sys.version.split()[0]} "
                f"· {os.cpu_count()} cores (using {NPROC} workers) · "
                f"{mem_available_mb()} MB available\n\n")
        f.write("Attacks: (1) independent heap frontier ≤ 9²², (2) preimage attack on "
                "the P ≥ 10 frontier, (3) 2.2M-sample Monte Carlo with len ≤ 600, "
                "(4) DP brute sanity to 10⁸.\n\n---\n")
    section_gates()
    S, Ps, F10, F9 = attack1()
    attack2(S, Ps, F10, F9)
    attack3()
    attack4()
    bug_report()
    verdict()
    log("")
    log("=" * 70)
    log("RED TEAM SUMMARY —", "NO RED FLAGS." if not RED_FLAGS else f"{len(RED_FLAGS)} RED FLAG(S).")
    for r in RED_FLAGS:
        log("  !!", r)


if __name__ == "__main__":
    main()
