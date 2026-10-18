# Independent reviewer falsification search (rcs128-proof-r1). SPDX-License-Identifier: MIT
"""Necessary condition of the candidate theorem: the output has length <= W,
and every feasible output has length >= OPT_RC, so W >= OPT_RC must hold for
every input.  Search small inputs (biased to periodic / self-reversed texts)
for W < OPT_RC.  Also re-checks count domination against N_T + N_rho(T) for an
optimal T.  A negative search result is NOT a proof."""
import json
import random
import sys
from rc_counts import counts, opt_rc, make_rho

INVOLUTIONS = [
    {'a': 'a', 'b': 'b'},
    {'a': 'b', 'b': 'a'},
    {'a': 'a', 'b': 'b', 'c': 'c'},
    {'a': 'b', 'b': 'a', 'c': 'c'},
    {'a': 'b', 'b': 'a', 'c': 'd', 'd': 'c'},
    {'a': 'a', 'b': 'c', 'c': 'b'},
]


def occ(T, s):
    return sum(T[i:i + len(s)] == s for i in range(len(T) - len(s) + 1))


def gen(rng, cm):
    rho = make_rho(cm)
    alpha = sorted(cm)
    mode = rng.randrange(4)
    if mode == 0:
        # self-reversed primitive core: X + rho(X) or palindromic-type
        X = ''.join(rng.choice(alpha) for _ in range(rng.randrange(1, 4)))
        prim = X + rho(X) if rng.randrange(2) else X + rng.choice(alpha) + rho(X)
    elif mode == 1:
        prim = ''.join(rng.choice(alpha) for _ in range(rng.randrange(1, 5)))
    else:
        X = ''.join(rng.choice(alpha) for _ in range(rng.randrange(1, 3)))
        prim = X + rho(X)
    text = prim * (12 // max(1, len(prim)) + 3)
    if mode == 3:
        # splice two periodic texts
        Y = ''.join(rng.choice(alpha) for _ in range(rng.randrange(1, 4)))
        text = text[:rng.randrange(3, 10)] + (Y + rho(Y)) * 4
    words = []
    for _ in range(rng.randrange(1, 4)):
        a = rng.randrange(0, len(text) - 2)
        L = rng.randrange(2, 11)
        s = text[a:a + L]
        if rng.randrange(3) == 0:
            s = rho(s)
        words.append(s)
    return words


def main(seed, trials):
    rng = random.Random(seed)
    worst = None
    checked = 0
    for trial in range(trials):
        cm = INVOLUTIONS[trial % len(INVOLUTIONS)]
        words = gen(rng, cm)
        c = counts(words, cm, 'broad')
        opt, T = opt_rc(words, cm)
        rho = make_rho(cm)
        for s, v in c['m'].items():
            if s and v > occ(T, s) + occ(rho(T), s):
                print(json.dumps(dict(kind='DOMINATION_FAIL', words=words, cm=cm, s=s, m=v)))
                return 1
        checked += 1
        gap = c['W'] - opt
        if worst is None or gap < worst[0]:
            worst = (gap, words, cm, c['W'], opt)
        if c['W'] < opt:
            print(json.dumps(dict(kind='W_LT_OPT', words=words, cm=cm, W=c['W'], opt=opt, T=T)))
            return 1
    print(json.dumps(dict(seed=seed, trials=checked, min_W_minus_OPT=worst[0],
                          witness=dict(words=worst[1], cm=worst[2], W=worst[3], OPT=worst[4]),
                          meaning='no W<OPT_RC and no domination failure in this bounded search; not a proof')))
    return 0


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]), int(sys.argv[2])))
