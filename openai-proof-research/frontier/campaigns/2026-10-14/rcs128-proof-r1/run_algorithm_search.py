# Independent reviewer harness (rcs128-proof-r1). SPDX-License-Identifier: MIT
"""Run the reviewer's executable model on random small inputs over several
explicit involutions and transition seeds.  Reports branch coverage and the first
assertion failure (with full input) if any.  Finite diagnostics only."""
import json
import random
import sys
import traceback
from collections import Counter
from rc_algorithm import solve, Fail
from rc_counts import make_rho, opt_rc

INV = [
    {'a': 'a', 'b': 'b'},
    {'a': 'b', 'b': 'a'},
    {'a': 'a', 'b': 'b', 'c': 'c'},
    {'a': 'b', 'b': 'a', 'c': 'c'},
    {'a': 'b', 'b': 'a', 'c': 'd', 'd': 'c'},
    {'a': 'a', 'b': 'c', 'c': 'b'},
]


def gen(rng, cm):
    rho = make_rho(cm)
    alpha = sorted(cm)
    texts = []
    for _ in range(rng.randrange(1, 4)):
        mode = rng.randrange(6)
        X = ''.join(rng.choice(alpha) for _ in range(rng.randrange(1, 4)))
        if mode >= 4:
            # nested periodicity: long run of a short period inside a longer period
            Xs = X[:rng.randrange(1, 3)]
            Y = ''.join(rng.choice(alpha) for _ in range(rng.randrange(1, 3)))
            prim = Xs * rng.randrange(3, 6) + Y
            if mode == 5:
                prim = prim + rho(prim)
        elif mode == 0:
            prim = X + rho(X)
        elif mode == 1:
            prim = X + rng.choice(alpha) + rho(X)
        elif mode == 2:
            prim = X
        else:
            prim = ''.join(rng.choice(alpha) for _ in range(rng.randrange(2, 6)))
        texts.append(prim * (24 // len(prim) + 2))
    words = []
    for _ in range(rng.randrange(1, 5)):
        tx = rng.choice(texts)
        if rng.randrange(3) == 0:
            tx = tx[:rng.randrange(2, 9)] + rng.choice(texts)
        a = rng.randrange(0, len(tx) - 3)
        s = tx[a:a + rng.randrange(2, 17)]
        if rng.randrange(3) == 0:
            s = rho(s)
        if rng.randrange(25) == 0:
            s = ''
        words.append(s)
    if rng.randrange(30) == 0:
        words.append(words[0])
    return words


def gen_nested(rng, cm):
    """child period-p runs embedded in longer-period host texts (request-prone)"""
    rho = make_rho(cm)
    alpha = sorted(cm)
    X = ''.join(rng.choice(alpha) for _ in range(rng.randrange(1, 3)))
    if rng.randrange(2):
        X = X + rho(X) if len(X) == 1 else X
    words = []
    m = rng.randrange(4, 9)
    words.append((X * 12)[:rng.randrange(len(X) * 3, len(X) * m + 1)])
    for _ in range(rng.randrange(1, 4)):
        Y = ''.join(rng.choice(alpha) for _ in range(rng.randrange(1, 3)))
        j = rng.randrange(3, 7)
        prim = X * j + Y
        if rng.randrange(3) == 0:
            prim = prim + rho(prim)
        tx = prim * 4
        a = rng.randrange(0, len(prim))
        s = tx[a:a + rng.randrange(len(prim), min(len(tx) - a, 2 * len(prim) + 4) + 1)]
        words.append(rho(s) if rng.randrange(3) == 0 else s)
    if rng.randrange(2):
        words.append((X * 12)[:rng.randrange(2, len(X) * 4 + 1)] + rng.choice(alpha))
    return words


def gen_req(rng, cm):
    """long runs of a short period X inside several distinct longer contexts"""
    rho = make_rho(cm)
    alpha = sorted(cm)
    X = rng.choice(alpha) if rng.randrange(2) else ''.join(rng.choice(alpha) for _ in range(2))
    words = []
    for _ in range(rng.randrange(2, 5)):
        L = rng.choice(alpha); Rr = rng.choice(alpha)
        run = X * rng.randrange(2, 7)
        w = ''.join(rng.choice(alpha) for _ in range(rng.randrange(0, 3))) + L + run + Rr
        w += ''.join(rng.choice(alpha) for _ in range(rng.randrange(0, 3)))
        words.append(rho(w) if rng.randrange(3) == 0 else w)
    return words


def main(seed, trials, check_opt=False):
    rng = random.Random(seed)
    cov = Counter()
    n = 0
    for trial in range(trials):
        cm = INV[trial % len(INV)]
        words = [gen, gen_nested, gen_req][trial % 3](rng, cm)
        tseed = rng.randrange(10 ** 6)
        try:
            T, M = solve(words, cm, tseed)
        except Fail as e:
            print(json.dumps(dict(kind='ASSERTION', msg=str(e), words=words, cm=cm, seed=tseed)))
            return 1
        except Exception:
            print(json.dumps(dict(kind='CRASH', words=words, cm=cm, seed=tseed, tb=traceback.format_exc())))
            return 2
        rho = make_rho(cm)
        assert all((not s) or s in T or rho(s) in T for s in words)
        if check_opt:
            o, _ = opt_rc(words, cm)
            assert len(T) <= 2 * o, (words, cm, T, o)
        cov.update(M.log)
        n += 1
    print(json.dumps(dict(seed=seed, instances=n, coverage=dict(sorted(cov.items())),
                          meaning='no assertion failure in this bounded run; not a proof')))
    return 0


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]), int(sys.argv[2]), len(sys.argv) > 3))
