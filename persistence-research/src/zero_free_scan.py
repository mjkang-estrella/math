#!/usr/bin/env python3
"""Agent B -- zero-digit-free 7-smooth numbers.

GOAL (SPEC.md Theorem 1; notes/theory.md Theorem 4): the persistence conjecture
is equivalent to "every 7-smooth number has P <= 10", and Theorem 4 reduces the
full conjecture to the single digit statement

    "every 7-smooth number with more than Z decimal digits contains the
     digit 0",   Z = max digit-length of a zero-free 7-smooth number,

PROVIDED the finite part (all 7-smooth m with len(m) <= Z have P <= 10) is
verified by the lattice searcher.  This module determines Z empirically, as
thoroughly as possible, and states exactly which ranges were covered.

Scans performed
  1. Pure powers  2^a (a <= A2), 3^b, 5^c, 7^d  by incremental m *= p with
     str(m) scanned for '0' (bounds chosen so all four reach ~60k digits).
  2. The FULL 4-prime exponent lattice {2^a 3^b 5^c 7^d < 10^500}, i.e. every
     7-smooth number with at most 500 digits.  This SUBSUMES all pairs at
     <= 500 digits and all triples and the quadruple at <= 500 digits (the
     task brief asked pairs <= 500, triples/quad <= 250; we exceed it).
  3. Standalone pair/triple scans at the brief's budgets, used as independent
     cross-checks of the big scan's slices.

Trailing-zero lemma (proved; gated below).  If 2|m and 5|m then 10|m, so
str(m) ends in '0'.  Hence every lattice point with a >= 1 AND c >= 1 is
provably NOT zero-free.  The 500-digit quadruple (~3.07e10 naive points)
therefore reduces to exactly its two faces

    {c = 0}  =  lattice (2,3,7)   and   {a = 0}  =  lattice (3,5,7),

about 2.46e8 string tests (~99.2% of the space pruned with no string test).
Correctness is enforced by Gate 3 (pruned == unpruned == brute force over all
7-smooth < 10^6) and Gate 4 (random tuples).

Every hit is recorded as (digit_length, (a,b,c,d)); m is regenerated from the
exponents at aggregation time and len(str(m)) is asserted == digit_length.

Usage:  python3 src/zero_free_scan.py     (resumable; state kept in results/)
"""
import json
import math
import random
import sys
import time
from multiprocessing import Pool
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.set_int_max_str_digits(0)          # 60k-digit str() needs this

from persistence import is_7smooth, smooth   # shared core (read-only)

# ---------------------------------------------------------------------------
# configuration
# ---------------------------------------------------------------------------
HERE = Path(__file__).resolve().parent
RESULTS = HERE.parent / "results"
HITS_PATH = RESULTS / "zero_free_hits.jsonl"
STATE_PATH = RESULTS / ".zero_free_state.json"
LIST_PATH = RESULTS / "zero_free_list.txt"
POWERS_PATH = RESULTS / "zero_free_powers.txt"
MD_PATH = RESULTS / "zero_free_results.md"

POW_BOUNDS = {2: 200_000, 3: 127_000, 5: 86_000, 7: 71_200}
QUAD_D = 500        # exhaustive digit-length for the FULL lattice (faces)
PAIR_D = 500        # brief's budget for pairs (standalone cross-checks)
TRI_D = 250         # brief's budget for triples (standalone cross-checks)
N_WORKERS = 32
TARGET_SHARD_S = 20.0     # aim: no single task dominates a worker for long
US_PER_PT = 5.0           # rough cost of one lattice point (str + loop)
STR_TIME_BUDGET_S = 900   # wall budget for the power phase before shrinking
PRIME_SLOT = {2: 0, 3: 1, 5: 2, 7: 3}
# Fixed cost model for DETERMINISTIC shard boundaries (resume-safety): the
# measured fit varies run-to-run and must not change the task list.
SHARD_C_US = 1.0e-3       # us per digit**SHARD_ALPHA
SHARD_ALPHA = 1.43


# ---------------------------------------------------------------------------
# zero tests
# ---------------------------------------------------------------------------
def zero_free_naive(n: int) -> bool:
    """Reference zero-test: extract digits by divmod, no str()."""
    if n == 0:
        return False
    while n:
        n, r = divmod(n, 10)
        if r == 0:
            return False
    return True


# ---------------------------------------------------------------------------
# scanners (run inside worker processes)
# ---------------------------------------------------------------------------
def power_scan(p: int, lo: int, hi: int):
    """0-free pure powers p^e, e in [lo, hi).  Incremental m *= p."""
    hits = []
    n_tests = 0
    m = p ** lo
    for e in range(lo, hi):
        n_tests += 1
        s = str(m)
        if "0" not in s:
            hits.append((len(s), e))
        m *= p
    return hits, n_tests


def lattice_scan(primes, D, lo0=0, hi0=None, prune=True):
    """Every exponent tuple e >= 0 with prod(primes[i]**e[i]) < 10**D.

    Returns (hits, n_tests): hits = [(digit_length, exponent_tuple)] for
    zero-free m; n_tests = number of string tests (leaves visited).
    The exponent of primes[0] is restricted to range(lo0, hi0).

    Trailing-zero lemma (prune=True): if 2 and 5 are both among the primes and
    the prefix has already assigned exponent >= 1 to one of them, then giving
    exponent >= 1 to the other makes 10 | m and str(m) ends in '0'; that value
    and all later ones are skipped (m only grows with the exponent).
    """
    LIMIT = 10 ** D
    k = len(primes)
    hits = []
    exps = [0] * k
    n_tests = 0
    if prune and 2 in primes and 5 in primes:
        later = max(primes.index(2), primes.index(5))
        other = min(primes.index(2), primes.index(5))
    else:
        later, other = -1, -1
    last = k - 1

    def rec(i, m):
        nonlocal n_tests
        p = primes[i]
        if i == last:                      # hot path: leaf level, inlined
            e = lo0 if i == 0 else 0
            mm = m * p ** e
            stop = prune and i == later and exps[other] >= 1
            while mm < LIMIT:
                n_tests += 1
                s = str(mm)
                if "0" not in s:
                    exps[i] = e
                    hits.append((len(s), tuple(exps)))
                if stop:                   # lemma: e >= 1 adds the missing 2/5
                    break
                mm *= p
                e += 1
            return
        if prune and i == later and exps[other] >= 1:
            exps[i] = 0                    # only e = 0 can be zero-free here
            rec(i + 1, m)
            return
        e = lo0 if i == 0 else 0
        mm = m * p ** e
        while mm < LIMIT and (hi0 is None or i != 0 or e < hi0):
            exps[i] = e
            rec(i + 1, mm)
            mm *= p
            e += 1

    rec(0, 1)
    return hits, n_tests


def worker(task):
    """Dispatch one task; returns (task_id, hits, n_tests)."""
    if task["kind"] == "power":
        hits, nt = power_scan(task["p"], task["lo"], task["hi"])
    else:
        hits, nt = lattice_scan(task["primes"], task["D"],
                                task.get("lo0", 0), task.get("hi0"),
                                prune=task.get("prune", True))
    return task["id"], hits, nt


# ---------------------------------------------------------------------------
# sanity gates (printed BEFORE any results)
# ---------------------------------------------------------------------------
def run_gates():
    # Gate 1 -- 2^0 .. 2^10
    hits, _ = power_scan(2, 0, 11)
    zs = sorted(e for _, e in hits)
    assert zs == list(range(10)), f"gate1: 0-free exponents {zs}"
    assert "0" in str(2 ** 10) and not zero_free_naive(2 ** 10)
    print("GATE 1 OK: 2^0..2^9 zero-free (1,2,4,...,512); 2^10=1024 has '0'")

    # Gate 2 -- scanner zero-test vs naive divmod scan, 1000 random ints
    rng = random.Random(0xC0FFEE)
    for _ in range(1000):
        x = rng.getrandbits(rng.randrange(2, 4096))
        assert ("0" in str(x)) == (not zero_free_naive(x)), x
    print("GATE 2 OK: zero-test agrees with naive divmod scan on 1000 random ints")

    # Gate 3 -- pruned == unpruned == brute force, all 7-smooth < 10^6
    t0 = time.perf_counter()
    truth = {m for m in range(1, 10 ** 6) if "0" not in str(m) and is_7smooth(m)}
    got_pruned, _ = lattice_scan((2, 3, 5, 7), 6, prune=True)
    got_plain, _ = lattice_scan((2, 3, 5, 7), 6, prune=False)
    assert {smooth(*e) for _, e in got_pruned} == truth
    assert {smooth(*e) for _, e in got_plain} == truth
    print(f"GATE 3 OK: pruned == unpruned == brute force over all 7-smooth < 10^6 "
          f"({len(truth)} zero-free; {time.perf_counter() - t0:.1f} s)")

    # Gate 4 -- lemma classification on 500 random exponent tuples
    rng = random.Random(271828)
    for _ in range(500):
        a, b, c, d = (rng.randrange(0, 14) for _ in range(4))
        m = smooth(a, b, c, d)
        if a >= 1 and c >= 1:
            assert "0" in str(m), (a, b, c, d, m)
    print("GATE 4 OK: 500 random tuples: a>=1 and c>=1 always implies '0' in str(m)")


# ---------------------------------------------------------------------------
# str() benchmark and bound adjustment
# ---------------------------------------------------------------------------
def benchmark_str():
    print(f"str() benchmark (CPython {sys.version.split()[0]}):")
    pts = []
    for d, reps in ((500, 20000), (2000, 5000), (10000, 400),
                    (30000, 100), (60000, 40), (120000, 15)):
        x = 10 ** d - 3
        t0 = time.perf_counter()
        for _ in range(reps):
            s = str(x)
        us = (time.perf_counter() - t0) / reps * 1e6
        assert len(s) == d
        pts.append((d, us))
        print(f"  {d:>7} digits: {us:9.2f} us/str()")
    (d1, t1), (d2, t2) = pts[2], pts[4]            # 10k and 60k digits
    alpha = math.log(t2 / t1) / math.log(d2 / d1)
    c_us = t1 / d1 ** alpha                        # us per digit**alpha
    print(f"  fit: t(us) = {c_us:.4e} * digits^{alpha:.3f}")
    proj = {}
    for p, E in POW_BOUNDS.items():
        l10 = math.log10(p)
        proj[p] = c_us * l10 ** alpha * (E + 1) ** (alpha + 1) / (alpha + 1) / 1e6  # seconds
        print(f"  projected str-time  {p}^e, e <= {E}: {proj[p]:8.0f} s single-core"
              f"  (max {int(E * l10) + 1} digits)")
    total = sum(proj.values())
    print(f"  total projected {total:.0f} core-s  ->  ~{total / N_WORKERS:.0f} s "
          f"wall on {N_WORKERS} workers")
    if total / N_WORKERS > STR_TIME_BUDGET_S:      # too slow: shrink bounds
        scale = (STR_TIME_BUDGET_S * N_WORKERS / total) ** (1.0 / (alpha + 1))
        for p in POW_BOUNDS:
            POW_BOUNDS[p] = max(1000, int(POW_BOUNDS[p] * scale))
        print(f"  !! over budget: exponent bounds scaled by {scale:.3f} -> {POW_BOUNDS}")
    return c_us, alpha, proj


# ---------------------------------------------------------------------------
# sharding helpers
# ---------------------------------------------------------------------------
def balanced_ranges(costs, k):
    """Split index range into <= k contiguous ranges of ~equal total cost."""
    n = len(costs)
    if n == 0:
        return []
    total = float(sum(costs))
    if k <= 1 or total <= 0:
        return [(0, n)]
    out, start, acc, target = [], 0, 0.0, total / k
    for i, c in enumerate(costs):
        acc += c
        if acc >= target and i + 1 < n:
            out.append((start, i + 1))
            start = i + 1
            acc = 0.0
    if start < n:
        out.append((start, n))
    return out


# pair/triple tasks get their position in (a,b,c,d) space here
SLOTS = {(2, 3): (0, 1), (2, 5): (0, 2), (2, 7): (0, 3),
         (3, 5): (1, 2), (3, 7): (1, 3), (5, 7): (2, 3),
         (2, 3, 5): (0, 1, 2), (2, 3, 7): (0, 1, 3),
         (2, 5, 7): (0, 2, 3), (3, 5, 7): (1, 2, 3),
         (2, 3, 5, 7): (0, 1, 2, 3)}


def build_tasks():
    tasks = []
    # 1. pure powers, cost-balanced shards (fixed cost model: deterministic)
    for p, E in POW_BOUNDS.items():
        dlens = [int(e * math.log10(p)) + 1 for e in range(E + 1)]
        costs = [dl ** SHARD_ALPHA for dl in dlens]
        total_s = SHARD_C_US * sum(costs) / 1e6
        K = max(4, min(40, int(total_s / TARGET_SHARD_S)))
        for lo, hi in balanced_ranges(costs, K):
            tasks.append({"kind": "power", "p": p, "lo": lo, "hi": hi,
                          "id": f"pow{p}:{lo}-{hi}"})
    # 2. faces of the 500-digit quadruple (trailing-zero lemma); shard by the
    #    largest exponent (level-0 exponent of each face)
    B = QUAD_D * math.log(10)
    for primes, role in (((2, 3, 7), "face237"), ((3, 5, 7), "face357")):
        l0, l1, l2 = (math.log(x) for x in primes)
        emax = int(B / l0) + 1
        per = [max(0.0, (B - e * l0) ** 2 / (2 * l1 * l2)) for e in range(emax + 1)]
        K = max(8, min(240, int(sum(per) * US_PER_PT / 1e6 / TARGET_SHARD_S)))
        for lo, hi in balanced_ranges(per, K):
            tasks.append({"kind": "lattice", "primes": primes, "D": QUAD_D,
                          "lo0": lo, "hi0": hi, "slots": SLOTS[primes],
                          "role": role, "id": f"{role}:{lo}-{hi}"})
    # 3. standalone pairs at 500 digits (cross-checks)
    for primes in ((2, 3), (2, 5), (2, 7), (3, 5), (3, 7), (5, 7)):
        tasks.append({"kind": "lattice", "primes": primes, "D": PAIR_D,
                      "slots": SLOTS[primes], "prune": True, "role": "pair",
                      "id": f"pair{''.join(map(str, primes))}D{PAIR_D}"})
    # 4. standalone interior triples at 250 digits (cross-checks)
    for primes in ((2, 3, 5), (2, 5, 7)):
        tasks.append({"kind": "lattice", "primes": primes, "D": TRI_D,
                      "slots": SLOTS[primes], "prune": True, "role": "tri",
                      "id": f"tri{''.join(map(str, primes))}D{TRI_D}"})
    return tasks


# ---------------------------------------------------------------------------
# persistence (resumability); hits are stored already mapped to (a,b,c,d)
# ---------------------------------------------------------------------------
def load_state():
    done, records, ntests = set(), [], {}
    if HITS_PATH.exists():
        with HITS_PATH.open() as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                obj = json.loads(line)
                records.extend((d, *abc, obj["tid"]) for d, abc in obj["hits"])
                ntests[obj["tid"]] = obj["nt"]
    if STATE_PATH.exists():
        done = set(json.loads(STATE_PATH.read_text()).get("done", []))
    return done, records, ntests


def save_task(tid, mapped, nt, done):
    with HITS_PATH.open("a") as f:
        f.write(json.dumps({"tid": tid, "nt": nt,
                            "hits": [[d, list(e)] for d, e in mapped]}) + "\n")
    done.add(tid)
    tmp = STATE_PATH.with_suffix(".tmp")
    tmp.write_text(json.dumps({"done": sorted(done)}))
    tmp.replace(STATE_PATH)


# ---------------------------------------------------------------------------
# Gate 5: standalone pair/triple scans vs slices of the face scans.
# All sets live in (dlen, a, b, c, d) space.
# ---------------------------------------------------------------------------
def cross_check_gates(records):
    def scan_set(tid, dmax=None):
        return {(d, a, b, c, dd) for d, a, b, c, dd, t in records
                if t == tid and (dmax is None or d <= dmax)}

    def face_slice(face_tid, fixed, dmax=None):
        out = set()
        for d, a, b, c, dd, t in records:
            if not t.startswith(face_tid):
                continue
            if dmax is not None and d > dmax:
                continue
            v = (a, b, c, dd)
            if all(v[i] == val for i, val in fixed.items()):
                out.add((d, a, b, c, dd))
        return out

    F237, F357 = "face237", "face357"
    checks = [
        ("pair (2,3)@500 == face237 slice d=0",
         scan_set(f"pair23D{PAIR_D}"), face_slice(F237, {3: 0})),
        ("pair (2,7)@500 == face237 slice b=0",
         scan_set(f"pair27D{PAIR_D}"), face_slice(F237, {1: 0})),
        ("pair (3,5)@500 == face357 slice d=0",
         scan_set(f"pair35D{PAIR_D}"), face_slice(F357, {3: 0})),
        ("pair (3,7)@500 == face357 slice c=0",
         scan_set(f"pair37D{PAIR_D}"), face_slice(F357, {2: 0})),
        ("pair (2,5)@500 == face237(b=d=0) U face357(b=d=0)",
         scan_set(f"pair25D{PAIR_D}"),
         face_slice(F237, {1: 0, 3: 0}) | face_slice(F357, {1: 0, 3: 0})),
        ("pair (5,7)@500 == face357 slice b=0",
         scan_set(f"pair57D{PAIR_D}"), face_slice(F357, {1: 0})),
        ("triple (2,3,5)@250 == face237(d=0) U face357(d=0)",
         scan_set(f"tri235D{TRI_D}", TRI_D),
         face_slice(F237, {3: 0}, TRI_D) | face_slice(F357, {3: 0}, TRI_D)),
        ("triple (2,5,7)@250 == face237(b=0) U face357(b=0)",
         scan_set(f"tri257D{TRI_D}", TRI_D),
         face_slice(F237, {1: 0}, TRI_D) | face_slice(F357, {1: 0}, TRI_D)),
    ]
    for name, A, Bset in checks:
        assert A == Bset, (f"GATE 5 FAILED: {name}: |A|={len(A)} |B|={len(Bset)};"
                           f" A-B={sorted(A - Bset)[:3]} B-A={sorted(Bset - A)[:3]}")
        print(f"GATE 5 OK: {name}  ({len(A)} hits)")


# ---------------------------------------------------------------------------
def aggregate(records):
    """Deduplicate hits by the decimal string; verify each against its exponents."""
    uniq = {}
    dup = 0
    for dlen, a, b, c, d, _tid in records:
        s = str(smooth(a, b, c, d))
        assert len(s) == dlen, f"dlen mismatch: recorded {dlen}, actual {len(s)} for {(a,b,c,d)}"
        if s in uniq:
            dup += 1
        uniq[s] = (a, b, c, d)
    return uniq, dup


def fmt_exp(e):
    return f"({e[0]},{e[1]},{e[2]},{e[3]})"


def main():
    t0 = time.perf_counter()
    RESULTS.mkdir(exist_ok=True)
    print("=" * 72)
    print("Agent B -- zero-free 7-smooth scan")
    print("=" * 72)

    print("\n--- sanity gates ---")
    run_gates()

    print("\n--- str() benchmark ---")
    c_us, alpha, proj = benchmark_str()

    done, records, ntests = load_state()
    tasks = build_tasks()
    tasks_by_id = {t["id"]: t for t in tasks}
    pending = [t for t in tasks if t["id"] not in done]
    print(f"\n--- run plan: {len(tasks)} tasks "
          f"({len(pending)} pending, {len(done)} already done) ---")

    t_run = time.perf_counter()
    if pending:
        with Pool(N_WORKERS) as pool:
            for tid, hits, nt in pool.imap_unordered(worker, pending, chunksize=1):
                t = tasks_by_id[tid]
                mapped = []
                if t["kind"] == "power":
                    slot = PRIME_SLOT[t["p"]]
                    for dlen, e in hits:
                        abc = [0, 0, 0, 0]
                        abc[slot] = e
                        mapped.append((dlen, tuple(abc)))
                else:
                    for dlen, exps in hits:
                        abc = [0, 0, 0, 0]
                        for si, ev in zip(t["slots"], exps):
                            abc[si] = ev
                        mapped.append((dlen, tuple(abc)))
                save_task(tid, mapped, nt, done)
                ntests[tid] = nt
                records.extend((d, *abc, tid) for d, abc in mapped)
                print(f"    done {tid:<22} hits={len(hits):>5} tests={nt:>12,} "
                      f"elapsed={time.perf_counter() - t_run:7.1f}s")
    t_scan = time.perf_counter() - t_run

    print("\n--- Gate 5: cross-checks of faces vs standalone scans ---")
    cross_check_gates(records)

    print("\n--- aggregation ---")
    uniq, dup = aggregate(records)
    total_tests = sum(ntests.get(t["id"], 0) for t in tasks)
    print(f"    records={len(records):,}  distinct zero-free 7-smooth={len(uniq):,}"
          f"  (cross-scan duplicates absorbed: {dup:,})")
    print(f"    total string tests: {total_tests:,}")

    Z = max(len(s) for s in uniq)
    argmax = sorted(s for s in uniq if len(s) == Z)
    prime_max = {}
    for s, exps in uniq.items():
        for slot, p in enumerate((2, 3, 5, 7)):
            rest = [exps[i] for i in range(4) if i != slot]
            if not any(rest) and exps[slot] > prime_max.get(p, (-1, ""))[0]:
                prime_max[p] = (exps[slot], s)
    prime_max = {p: prime_max.get(p, (0, "1")) for p in (2, 3, 5, 7)}

    buckets = {}
    for s in uniq:
        buckets[len(s) // 10] = buckets.get(len(s) // 10, 0) + 1

    # artifacts -------------------------------------------------------------
    with LIST_PATH.open("w") as f:
        for s in sorted((s for s in uniq if len(s) >= 40),
                        key=lambda x: (len(x), x)):
            f.write(f"{s} {fmt_exp(uniq[s])}\n")
    with POWERS_PATH.open("w") as f:
        for p in (2, 3, 5, 7):
            slot = PRIME_SLOT[p]
            f.write(f"# 0-free powers of {p} (e, digit-length), e <= {POW_BOUNDS[p]}\n")
            for s, exps in sorted(uniq.items(), key=lambda x: (len(x[0]), x[0])):
                rest = [exps[i] for i in range(4) if i != slot]
                if not any(rest):
                    f.write(f"{p}^{exps[slot]} {len(s)} digits  {s}\n")

    # coverage facts --------------------------------------------------------
    cov = {p: len(str(p ** POW_BOUNDS[p])) for p in (2, 3, 5, 7)}
    B500 = QUAD_D * math.log(10)
    naive_quad500 = B500 ** 4 / (24 * math.log(2) * math.log(3) * math.log(5) * math.log(7))
    face_pts = sum(ntests.get(t["id"], 0) for t in tasks if t.get("role", "").startswith("face"))
    pair_pts = sum(ntests.get(t["id"], 0) for t in tasks if t.get("role") == "pair")
    tri_pts = sum(ntests.get(t["id"], 0) for t in tasks if t.get("role") == "tri")
    pow_pts = sum(ntests.get(t["id"], 0) for t in tasks if t["kind"] == "power")

    note86 = ("(matches the literature-known largest zero-free power of 2, 2^86)"
              if prime_max[2][0] == 86 else
              "(NOTE: literature cites 2^86 as the largest zero-free power of 2 -- "
              "investigate if this disagrees!)")
    warn = ("\n**WARNING: Z >= 500 -- the exhaustive lattice scan must be re-run at"
            " larger D before Theorem 4 can use this Z.**\n" if Z >= QUAD_D else "")

    bucket_rows = "".join(
        f"| {max(lo * 10, 1)}-{lo * 10 + 9} | {buckets[lo]} |\n" for lo in sorted(buckets))
    am0 = uniq[argmax[0]]

    md = f"""# Zero-free 7-smooth numbers (Agent B)

Run {time.strftime('%Y-%m-%d %H:%M:%S')}, wall {time.perf_counter() - t0:.0f} s total
(scan phase {t_scan:.0f} s), Python {sys.version.split()[0]}, {N_WORKERS} workers,
pure stdlib + `src/persistence.py`.

## Headline

**Z = {Z}** -- the largest decimal digit-length of any zero-free 7-smooth number
found by any scan below.  It is attained by

    {argmax[0]}
    = 2^{am0[0]} * 3^{am0[1]} * 5^{am0[2]} * 7^{am0[3]}
    exponent tuple (a,b,c,d) = {fmt_exp(am0)}

{f'So, empirically, the conjecture reduces to: *every 7-smooth number with more than {Z} digits contains the digit 0* (Theorem 4), pending the finite part for len(m) <= {Z} (lattice searcher).' if len(argmax) == 1 else f'{len(argmax)} distinct numbers attain this length.'}
{warn}
Largest zero-free pure powers (complete lists in `zero_free_powers.txt`):

| prime | max 0-free exponent | digit length | the number |
|---|---|---|---|
| 2 | {prime_max[2][0]} | {len(prime_max[2][1])} | `{prime_max[2][1]}` |
| 3 | {prime_max[3][0]} | {len(prime_max[3][1])} | `{prime_max[3][1]}` |
| 5 | {prime_max[5][0]} | {len(prime_max[5][1])} | `{prime_max[5][1]}` |
| 7 | {prime_max[7][0]} | {len(prime_max[7][1])} | `{prime_max[7][1]}` |

{note86}

## Method

1. **Pure powers**: incremental `m *= p`, `s = str(m)`, `'0' in s` test, for
   2^a (a <= {POW_BOUNDS[2]}), 3^b (b <= {POW_BOUNDS[3]}), 5^c (c <= {POW_BOUNDS[5]}),
   7^d (d <= {POW_BOUNDS[7]}) -- max digit lengths
   {cov[2]}/{cov[3]}/{cov[5]}/{cov[7]}.
   Measured str() cost t(us) = {c_us:.3e} * digits^{alpha:.3f} (subquadratic,
   CPython {sys.version.split()[0]}); projected {sum(proj.values()):.0f} core-s,
   sharded into cost-balanced exponent ranges across {N_WORKERS} workers
   ({pow_pts:,} string tests).
2. **Full lattice to 500 digits**: every 2^a*3^b*5^c*7^d < 10^500 was
   classified.  **Trailing-zero lemma** (Gate 3/4 verified): if a >= 1 and
   c >= 1 then 10 | m, so m ends in '0' -- about
   {naive_quad500 - face_pts:.2e} of the ~{naive_quad500:.2e} naive lattice points
   ({100 * (1 - face_pts / naive_quad500):.1f}%) are pruned with no string test.  The remaining
   {face_pts:,} points are exactly the two faces {{c=0}} = lattice (2,3,7) and
   {{a=0}} = lattice (3,5,7), walked depth-first with incremental multiplies,
   sharded by the largest exponent (a, resp. b) across {N_WORKERS} workers.
   This SUBSUMES all pairs <= 500 digits, all triples <= 500 digits and the
   quadruple <= 500 digits (the brief's budgets were pairs 500,
   triples/quad 250 -- all exceeded).
3. **Cross-checks** (Gate 5): six standalone pair scans (<= 500 digits) and two
   standalone interior-triple scans (<= 250 digits; {pair_pts + tri_pts:,} further
   string tests) were run independently and compared, as sets, against the
   corresponding slices of the face scans.  All equal.

## Sanity gates (all printed before the run; source: `run_gates()`)

- GATE 1: 2^0..2^9 zero-free; 2^10 = 1024 contains '0'.
- GATE 2: zero-test agrees with a naive divmod digit scan on 1000 random ints.
- GATE 3: pruned == unpruned == brute-force enumeration of all 7-smooth < 10^6.
- GATE 4: 500 random exponent tuples: a >= 1 and c >= 1 always gives '0' in str(m).
- GATE 5: every standalone pair/triple scan equals its extraction from the faces.
- Every recorded hit is regenerated from (a,b,c,d); len(str(m)) is asserted.

## Zero-free 7-smooth numbers by digit-length bucket

| digit length | count |
|---|---|
{bucket_rows}
Total distinct zero-free 7-smooth numbers found: **{len(uniq):,}**
({pow_pts:,} pure-power tests, {face_pts + pair_pts + tri_pts:,} lattice tests).

## Coverage (what was exhaustively checked)

- **[1, 500] digits, exhaustive over the FULL 4-prime lattice**: no zero-free
  7-smooth number with digit-length in [{Z + 1}, 500] exists.  Every
  2^a*3^b*5^c*7^d < 10^500 was classified ({face_pts:,} string tests plus the
  lemma-pruned remainder, correctness gated as above).
- **Pure powers**: no zero-free 2^a for a <= {POW_BOUNDS[2]} ({cov[2]} digits),
  3^b for b <= {POW_BOUNDS[3]} ({cov[3]} digits), 5^c for c <= {POW_BOUNDS[5]}
  ({cov[5]} digits), 7^d for d <= {POW_BOUNDS[7]} ({cov[7]} digits) -- i.e. no
  zero-free pure power with digit-length in [{Z + 1}, ~60,000].
- **Two-prime products** are covered to 500 digits (inside the lattice scan);
  **three-prime products and the quadruple** likewise to 500 digits.
- Beyond those ranges: not covered empirically (handled by theory / the
  lattice searcher's completeness theorem).

## Artifacts

- `results/zero_free_results.md` -- this file
- `results/zero_free_list.txt` -- all zero-free 7-smooth numbers with >= 40
  digits: `<decimal> (a,b,c,d)` per line
- `results/zero_free_powers.txt` -- every 0-free pure power with digit length
- `results/zero_free_hits.jsonl` -- raw hits per task (resumable)
- `src/zero_free_scan.py` -- the scanner (gates, benchmark, scans, report)
"""
    MD_PATH.write_text(md)

    print(f"\nZ = {Z}; argmax: {argmax[0][:72]}{'...' if len(argmax[0]) > 72 else ''}")
    print(f"      = 2^{am0[0]}*3^{am0[1]}*5^{am0[2]}*7^{am0[3]}, {Z} digits")
    for p in (2, 3, 5, 7):
        print(f"      largest 0-free {p}^e: e = {prime_max[p][0]} "
              f"({len(prime_max[p][1])} digits)")
    print(f"Wrote {MD_PATH.name}, {LIST_PATH.name}, {POWERS_PATH.name}")


if __name__ == "__main__":
    main()
