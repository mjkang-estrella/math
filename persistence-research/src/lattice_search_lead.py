"""Lead agent's independent lattice searcher (cross-validates subagent A).

Proves: every m = 2^a*3^b*5^c*7^d with len23(a,b)+c+d <= D has P(m) <= 10
==> no integer < 10^D has persistence >= 12 (SPEC.md, Theorem 3).

Also collects zero-free digit-length statistics (feeds theory.md Theorem 5).

Usage: python3 src/lattice_search_lead.py [D] [minutes_budget]
"""
import json
import os
import sys
import time
from collections import Counter
from multiprocessing import Pool

sys.path.insert(0, "src")
from persistence import persistence, persistence_naive, len23_table, smooth, prime_digit_expansion

WORKERS = int(os.environ.get("WORKERS", "32"))


def domain_size(D, t23):
    total = 0
    for a in range(3 * D + 3):
        for b in range(2 * D + 3):
            l23 = t23[a][b]
            if l23 <= D:
                rem = D - l23
                total += (rem + 1) * (rem + 2) // 2
    return total


def per_a_points(D, t23):
    out = []
    for a in range(3 * D + 3):
        s = 0
        for b in range(2 * D + 3):
            l23 = t23[a][b]
            if l23 <= D:
                rem = D - l23
                s += (rem + 1) * (rem + 2) // 2
        out.append(s)
    return out


def shard_bounds(D, t23, nshards):
    """Cost-balanced [a_lo, a_hi) ranges."""
    pts = per_a_points(D, t23)
    total = sum(pts)
    target, shards, a_lo, acc = total / nshards, [], 0, 0
    for a, p in enumerate(pts):
        acc += p
        if acc >= target and a > a_lo:
            shards.append((a_lo, a + 1))
            a_lo, acc = a + 1, 0
    if a_lo < len(pts):
        shards.append((a_lo, len(pts)))
    return shards, total


def run_shard(args):
    D, a_lo, a_hi = args
    t23 = len23_table(3 * D + 3, 2 * D + 3)
    maxp, argmax, hist = 0, None, Counter()
    zerofree = Counter()          # digit-length -> count of 0-free m
    points = 0
    for a in range(a_lo, a_hi):
        mab = 2 ** a
        for b in range(2 * D + 3):
            l23 = t23[a][b]
            if l23 > D:
                continue
            rem = D - l23
            mc = mab * 3 ** b
            for c in range(rem + 1):
                m = mc
                for d in range(rem - c + 1):
                    points += 1
                    s = str(m)
                    ndig = len(s)
                    if "0" in s:
                        zerofree[ndig // 10 * 10] += 1
                    else:
                        p = persistence(m)
                        hist[p] += 1
                        if p > maxp:
                            maxp, argmax = p, (a, b, c, d, m)
                        elif p == maxp and argmax is not None and (a, b, c, d) != argmax[:4]:
                            pass
                    m *= 7
                mc *= 5
    return maxp, argmax, hist, zerofree, points


def main():
    D = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    budget_min = float(sys.argv[2]) if len(sys.argv) > 2 else 40.0
    t23 = len23_table(3 * D + 3, 2 * D + 3)
    size = domain_size(D, t23)
    shards, total_check = shard_bounds(D, t23, WORKERS * 4)
    assert total_check == size
    print(f"D={D}: exact domain size = {size:,} points, {len(shards)} shards", flush=True)

    # rate calibration on a TINY slice (a in [0,2) — representative large-rem cost)
    t0 = time.time()
    _ = run_shard((D, 0, 2))
    dt = time.time() - t0
    pts0 = sum(per_a_points(D, t23)[0:2])
    rate = pts0 / max(dt, 1e-9)
    proj_min = size / rate / WORKERS / 60
    print(f"calibration: {pts0:,} pts in {dt:.1f}s -> {rate:,.0f} pts/s/core "
          f"-> projected {proj_min:.1f} min on {WORKERS} workers", flush=True)
    if proj_min > budget_min:
        print(f"ABORT: projected {proj_min:.1f} min > budget {budget_min} min. Lower D.", flush=True)
        sys.exit(2)

    tasks = [(D,) + s for s in shards]
    gmaxp, garg, ghist, gzf, done, discoveries = 0, None, Counter(), Counter(), 0, []
    t0 = time.time()
    with Pool(WORKERS) as pool:
        for i, (maxp, argmax, hist, zf, pts) in enumerate(pool.imap_unordered(run_shard, tasks)):
            ghist += hist
            gzf += zf
            done += pts
            if maxp > gmaxp:
                gmaxp, garg = maxp, argmax
            if maxp >= 11:
                discoveries.append((maxp, argmax))
                a, b, c, d, m = argmax
                n = prime_digit_expansion(a, b, c, d)
                pn = persistence_naive(n)
                with open("results/COUNTEREXAMPLE.md", "a") as f:
                    f.write(f"# DISCOVERY: P({n}) >= 12\nm = {m} = 2^{a}*3^{b}*5^{c}*7^{d}\n"
                            f"P(m) = {maxp}, persistence_naive(n) = {pn}\n")
            if i % 8 == 0 or i == len(tasks) - 1:
                el = time.time() - t0
                eta = el / done * (size - done)
                print(f"[{done/size*100:5.1f}%] points={done:,} maxP={gmaxp} "
                      f"argmax={garg} elapsed={el/60:.1f}m eta={eta/60:.1f}m", flush=True)
                with open("results/lead_lattice_checkpoint.json", "w") as f:
                    json.dump({"D": D, "points_done": done, "size": size,
                               "maxP": gmaxp, "argmax": list(garg) if garg else None,
                               "hist": dict(ghist), "zerofree": {str(k): v for k, v in sorted(gzf.items())},
                               "discoveries": len(discoveries),
                               "elapsed_s": el}, f)

    print(f"\nFINAL D={D}: {size:,} points, max P(m) = {gmaxp} at {garg}", flush=True)
    print(f"histogram: {dict(sorted(ghist.items()))}", flush=True)
    print(f"zero-free counts by digit-length bucket: {dict(sorted(gzf.items()))}", flush=True)
    print(f"discoveries (P >= 11): {len(discoveries)}", flush=True)
    verdict = ("NO persistence-12 number exists below 10^%d" % D) if gmaxp <= 10 else \
              ("DISCOVERY! persistence-12 number exists: see results/COUNTEREXAMPLE.md")
    with open("results/lead_lattice_results.md", "w") as f:
        f.write(f"# Lead lattice search results (D={D})\n\n")
        f.write(f"- Exact domain size: {size:,} points (all m = 2^a*3^b*5^c*7^d "
                f"with len23(a,b)+c+d <= {D})\n")
        f.write(f"- Wall time: {(time.time()-t0)/60:.1f} min on {WORKERS} workers\n")
        f.write(f"- Max P(m) over the domain: **{gmaxp}** at (a,b,c,d) = {garg[:4] if garg else None}\n")
        f.write(f"- Histogram of P values: {dict(sorted(ghist.items()))}\n")
        f.write(f"- Zero-free m by digit-length bucket (x10): {dict(sorted(gzf.items()))}\n")
        f.write(f"- Discoveries (P >= 11): {len(discoveries)}\n\n")
        f.write(f"**Verdict (Theorem 3, SPEC.md): {verdict}.**\n")
    print(verdict, flush=True)


if __name__ == "__main__":
    main()
