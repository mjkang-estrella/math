#!/usr/bin/env python3
"""Exact exhaustive binary scans for distinct abelian-square factor maxima.

Coverage proof (construction):
  For binary words of length n the count is invariant under complement
  (bijective relabelling of letters) and reversal (bijective on factor strings,
  preserves the abelian-square property and distinctness).  These commute, so
  the group has at most 4 elements and canon(w) = min{w, ~w, rev w, rev ~w}
  is the unique minimal element of the orbit; canon is idempotent, hence
  {w in [0,2^n) : w == canon(w)} contains exactly one representative per orbit
  and scanning it covers EVERY binary word of length n.

Usage: exhaustive.py binary <n_lo> <n_hi> <out.json>
"""
import json, sys, time


def count_binary(w, n):
    P = [0] * (n + 1)
    for i in range(n):
        P[i + 1] = P[i] + ((w >> (n - 1 - i)) & 1)
    seen = set()
    for a in range(n - 1):
        Pa = P[a]
        for b in range(a + 2, n + 1, 2):
            m = (a + b) >> 1
            if 2 * P[m] == Pa + P[b]:
                L = b - a
                seen.add((L, (w >> (n - b)) & ((1 << L) - 1)))
    return len(seen)


def bits(w, n):
    return format(w, '0%db' % n)


def canon_mask(w, n):
    full = (1 << n) - 1
    comp = full ^ w
    s = format(w, '0%db' % n)
    cs = format(comp, '0%db' % n)
    rs = s[::-1]
    rcs = cs[::-1]
    return min(w, comp, int(rs, 2), int(rcs, 2))


def to_word(mask, n):
    return bits(mask, n)


def main():
    mode, n_lo, n_hi, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    assert mode == 'binary'
    res = {}
    for n in range(n_lo, n_hi + 1):
        t0 = time.time()
        best = -1; best_ws = []; n_orbits = 0; total = 1 << n
        full = (1 << n) - 1
        for w in range(total):
            comp = full ^ w
            s = format(w, '0%db' % n)
            if not (w == min(w, comp, int(s[::-1], 2), int(format(comp, '0%db' % n)[::-1], 2))):
                continue
            n_orbits += 1
            c = count_binary(w, n)
            if c > best:
                best = c; best_ws = [w]
            elif c == best:
                best_ws.append(w)
        dt = time.time() - t0
        res[str(n)] = {
            'n': n, 'total_words': total, 'orbits': n_orbits,
            'max_distinct_abelian_squares': best,
            'n_at_max': len(best_ws),
            'witnesses_bits': [bits(w, n) for w in best_ws[:8]],
            'seconds': round(dt, 2),
        }
        print(n, res[str(n)]['max_distinct_abelian_squares'], 'orbits=%d' % n_orbits, '%.1fs' % dt)
    json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
