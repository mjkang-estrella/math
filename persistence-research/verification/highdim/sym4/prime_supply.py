"""Bounded stdlib search for factors of 10**d-1, 1<=d<=60.

Search hints only: both certificate checkers prove primality/orders themselves.
Large unsplit factors are explicitly reported; no complete-factorization claim.
"""
import sys
sys.dont_write_bytecode = True
import collections
import json
import math
import pathlib
import time

HERE = pathlib.Path(__file__).resolve().parent


def save(name, data):
    p = HERE / name
    q = p.with_suffix(p.suffix + '.tmp')
    q.write_text(json.dumps(data, indent=1) + '\n')
    q.replace(p)


def probable(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    s, t = 0, n - 1
    while t % 2 == 0:
        s += 1
        t //= 2
    # Deterministic for n < 2**64; only a screen above that bound.
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, t, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def factor(n, deadline, found, unresolved):
    if n == 1:
        return
    if probable(n):
        (found if n < 2**64 else unresolved).append(n)
        return
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            found.append(p)
            factor(n // p, deadline, found, unresolved)
            return
    for c in range(1, 30):
        x = y = 2
        g = 1
        i = 0
        while g == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            g = math.gcd(abs(x - y), n)
            i += 1
            if i % 512 == 0 and time.monotonic() > deadline:
                unresolved.append(n)
                return
        if g != n:
            factor(g, deadline, found, unresolved)
            factor(n // g, deadline, found, unresolved)
            return
    unresolved.append(n)


def order(b, p):
    ff, unknown = [], []
    factor(p - 1, time.monotonic() + 2, ff, unknown)
    assert not unknown, (p, unknown)
    ans = p - 1
    for q in set(ff):
        while ans % q == 0 and pow(b, ans // q, p) == 1:
            ans //= q
    return ans


def main():
    baseline = json.loads((HERE.parent / 'supply_B.json').read_text())
    known = {r[0]: r for r in baseline}
    discoveries, stages = {}, []
    for d in range(1, 61):
        rem = 10**d - 1
        fs = []
        for p in (3, *sorted(known)):
            while rem % p == 0:
                fs.append(p)
                rem //= p
        unknown = []
        factor(rem, time.monotonic() + 1.0, fs, unknown)
        assert math.prod(fs + unknown) == 10**d - 1
        for p in set(fs):
            if 7 < p <= 10**14 and p not in known:
                row = [p, order(10, p), order(3, p), order(7, p)]
                known[p] = row
                discoveries[p] = row
        stages.append({'d': d, 'factors': sorted(fs), 'unresolved_or_large_probable': unknown})
        save('prime_search.json', {'max_d': d, 'cap': 10**14, 'stages': stages,
                                  'new': sorted(discoveries.values())})
        print('d', d, 'new', len(discoveries), 'unresolved', len(unknown), flush=True)
    supply = sorted(known.values())
    save('supply.json', supply)
    table = []
    for p, d, a, w in supply:
        if d <= 60:
            table.append({'p': p, 'decimal_order': d, 'order3': a, 'order7': w,
                          'index_3_7': (p-1)//math.lcm(a,w),
                          'tail3_periods': [100,20],
                          'tail3_step_index': (p-1)//math.lcm(a//math.gcd(a,100),w//math.gcd(w,20)),
                          'new': p in discoveries})
    save('prime_ranking.json', sorted(table, key=lambda r:(r['decimal_order'],-r['tail3_step_index'],r['p'])))
    print(json.dumps({'supply':len(supply),'new':sorted(discoveries.values())}))


if __name__ == '__main__':
    main()
