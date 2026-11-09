#!/usr/bin/env python3
"""k-ary distinct abelian-square factor tools.

Modes:
  exhaustive k n_lo n out.json   -- ALL k^n words, exact maxima (n small)
  search k n seconds seed out.json -- bounded seeded random restarts + steepest
                                      ascent 1-position hill climbing. NOT
                                      exhaustive; reported as best-found only.

Distinctness on literal strings (see abecount.py); counters cross-validated.
"""
import json, random, sys, time, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from abecount import count_asq_A


def count_k(t, n, k):
    """Fast k-ary counter on tuple word. Square iff equal halves' count-vectors."""
    P = [tuple([0] * k)]
    for ch in t:
        row = list(P[-1]); row[ch] += 1; P.append(tuple(row))
    K = range(k)
    seen = set()
    for a in range(n - 1):
        Pa = P[a]
        for b in range(a + 2, n + 1, 2):
            m = (a + b) >> 1
            L = b - a
            left = P[m]; right = P[b]
            if all(left[c] - Pa[c] == right[c] - left[c] for c in K):
                seen.add((L, tuple(t[a:b])))
    return len(seen)


def exhaustive(k, n_lo, n_hi, out):
    res = {}
    for n in range(n_lo, n_hi + 1):
        t0 = time.time()
        best = -1; best_ws = []; total = k ** n
        for i in range(total):
            t = []
            x = i
            for _ in range(n):
                t.append(x % k); x //= k
            c = count_k(t, n, k)
            if c > best:
                best = c; best_ws = [tuple(t)]
            elif c == best:
                best_ws.append(tuple(t))
        dt = time.time() - t0
        res[str(n)] = {
            'n': n, 'alphabet': k, 'total_words': total,
            'max_distinct_abelian_squares': best,
            'n_at_max': len(best_ws),
            'witnesses': [''.join(map(str, w)) for w in best_ws[:8]],
            'seconds': round(dt, 2),
        }
        print('k=%d n=%d max=%d at=%d words=%d %.1fs' %
              (k, n, best, len(best_ws), total, dt))
    json.dump(res, open(out, 'w'), indent=1)


def score(t, n, k):
    return count_k(t, n, k)


def hillclimb(t, n, k, rng):
    cur = list(t); cs = score(cur, n, k)
    improved = True
    while improved:
        improved = False
        best_i, best_v, best_c = -1, None, cs
        for i in range(n):
            for v in range(k):
                if v == cur[i]:
                    continue
                old = cur[i]; cur[i] = v
                c = score(cur, n, k)
                cur[i] = old
                if c > best_c:
                    best_c, best_i, best_v = c, i, v
        if best_i >= 0:
            cur[best_i] = best_v; cs = best_c; improved = True
    return tuple(cur), cs


def search(k, n, seconds, seed, out):
    rng = random.Random(seed)
    t0 = time.time()
    tries = 0
    best = -1; best_w = None
    history = []
    # seed pool: random + structured
    seeds = [''.join(rng.choice('012'[:k]) for _ in range(n)) for _ in range(0, 0)]
    deadline = time.time() + seconds
    while time.time() < deadline:
        mode = tries % 3
        if mode == 0:
            t = tuple(rng.randrange(k) for _ in range(n))
        elif mode == 1:  # random perturbation of current best
            t = list(best_w) if best_w else [0] * n
            for _ in range(rng.randint(1, 4)):
                t[rng.randrange(n)] = rng.randrange(k)
            t = tuple(t)
        else:  # periodic / structured starts
            base = ''.join(str(i) for i in range(k)) * (n // k + 1)
            t = tuple(int(c) for c in base[:n])
            for _ in range(rng.randint(0, 6)):
                t = list(t); t[rng.randrange(n)] = rng.randrange(k); t = tuple(t)
        w, c = hillclimb(t, n, k, rng)
        tries += 1
        if c > best:
            best, best_w = c, w
            history.append({'try': tries, 'score': c,
                            'word': ''.join(map(str, w))})
    dt = time.time() - t0
    outd = {'mode': 'search', 'n': n, 'alphabet': k, 'seed': seed,
            'hillclimb_starts': tries, 'seconds': round(dt, 2),
            'best_found': best, 'best_word': ''.join(map(str, best_w)),
            'improvement_history': history,
            'exhaustive': False}
    json.dump(outd, open(out, 'w'), indent=1)
    print(json.dumps({x: outd[x] for x in ['n', 'alphabet', 'hillclimb_starts', 'best_found', 'best_word', 'seconds']}))


if __name__ == '__main__':
    m = sys.argv[1]
    if m == 'exhaustive':
        exhaustive(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
    else:
        k, n, sec, seed, out = int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
        search(k, n, sec, seed, out)
