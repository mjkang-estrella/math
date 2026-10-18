# SPDX-License-Identifier: MIT
"""Independent finite checks for the RCS128 contribution review.

Written by the contribution reviewer directly from the pinned source text
(02-counts.tex) and the candidate's stated rules. It imports no author code.
These are bounded finite diagnostics about whether simpler routes are
available; they are not proofs of the candidate or of any universal claim.
"""
import itertools
import json
import random
import sys


def rho_of(cm):
    return lambda s: ''.join(cm[c] for c in reversed(s))


def substrings(words):
    return {w[i:j] for w in words for i in range(len(w)) for j in range(i + 1, len(w) + 1)}


def b_count(A, s, r):
    """Source b_{A,s}(r); A is the one-period word, A(i)=A[i mod p]."""
    p = len(A)
    at = lambda i: A[i % p]
    n = 0
    for j in range(1, len(r) - len(s)):
        if r[j:j + len(s)] != s:
            continue
        if any(r[h] != at(h - j) for h in range(1, len(r) - 1)):
            continue
        if r[0] != at(-j) and r[-1] != at(len(r) - 1 - j):
            n += 1
    return n


def counts(required, alphabet, rho=None, rule='source'):
    """Descending forced counts.

    rule='source'   : ordinary source recursion (rho must be None).
    rule='naive'    : orbit maximum + even rounding, ordinary k+1 rules.
    rule='selftext' : as 'naive' but g=2k+1 for self-reversed periodic texts.
    """
    V = substrings(required)
    m = {}

    def B(A, s):
        return sum(b_count(A, s, r) * m[r] for r in V if len(r) >= len(s) + 2)

    def bounds(s):
        req = 0
        if s in required:
            req = 2 if (rho is not None and rho(s) == s) else 1
        val = max(req, sum(m.get(c + s, 0) for c in alphabet), sum(m.get(s + c, 0) for c in alphabet))
        for v in V:
            if len(v) <= len(s) or not v.startswith(s):
                continue
            for p in range(1, len(v)):
                d = len(v) - len(s)
                if d % p or any(v[i] != v[i % p] for i in range(len(v))):
                    continue
                k = d // p
                A = v[:p]
                if m[v] <= B(A, v):
                    continue
                g = k + 1
                if rule == 'selftext' and rho(A) in A + A:
                    g = 2 * k + 1
                val = max(val, B(A, s) + g)
        return val

    for s in sorted(V, key=lambda x: (-len(x), x)):
        if s in m:
            continue
        if rho is None:
            m[s] = bounds(s)
        else:
            val = max(bounds(s), bounds(rho(s)))
            if rho(s) == s:
                val += val % 2
            m[s] = m[rho(s)] = val
    return m, sum(m.get(a, 0) for a in alphabet)


def reduce_rc(words, rho):
    words = [w for w in words if w]
    orbits = {min(w, rho(w)): {w, rho(w)} for w in words}
    reps = sorted(orbits)
    keep = [r for r in reps if not any(o != r and any(x in y for x in orbits[r] for y in orbits[o]) for o in reps)]
    return keep


def opt_rc_bruteforce(reps, rho, alphabet, limit):
    for L in range(0, limit + 1):
        for t in itertools.product(alphabet, repeat=L):
            t = ''.join(t)
            if all(r in t or rho(r) in t for r in reps):
                return L, t
    return None, None


def ov(a, b):
    return max(k for k in range(min(len(a), len(b))) if a[len(a) - k:] == b[:k]) if a and b else 0


def merge_len(seq):
    if not seq:
        return 0
    return sum(len(x) for x in seq) - sum(ov(x, y) for x, y in zip(seq, seq[1:]))


def oriented(reps, rho, bits):
    return [rho(r) if b else r for r, b in zip(reps, bits)]


def substring_free(words):
    return all(not (a != b and a in b) for a in words for b in words) and len(set(words)) == len(words)


def analyse_orientations(reps, rho, alphabet):
    rows = []
    n = len(reps)
    for bits in itertools.product((0, 1), repeat=n):
        ws = oriented(reps, rho, bits)
        P = min(merge_len([ws[i] for i in perm]) for perm in itertools.permutations(range(n)))
        C = min(sum(len(ws[i]) - ov(ws[i], ws[s[i]]) for i in range(n))
                for s in itertools.permutations(range(n)) if all(s[i] != i for i in range(n)))
        _, W = counts(set(ws), alphabet, None, 'source')
        rows.append({'bits': ''.join(map(str, bits)), 'P': P, 'C': C, 'W': W})
    opt = min(r['P'] for r in rows)
    cmin = min(r['C'] for r in rows)
    mins = [r for r in rows if r['C'] == cmin]
    return rows, opt, cmin, mins


def main():
    out = {}
    # 1. Template obstruction: naive equivariant counts give W=6 < OPT_RC=7.
    cm = {'b': 'b', 'c': 'c'}
    rho = rho_of(cm)
    S = ['bbcbbc', 'bcbbcb', 'cbbcbb']
    reps = reduce_rc(S, rho)
    req = set(reps) | {rho(r) for r in reps}
    _, W_naive = counts(req, 'bc', rho, 'naive')
    _, W_self = counts(req, 'bc', rho, 'selftext')
    opt, witness = opt_rc_bruteforce(reps, rho, 'bc', 8)
    out['template_obstruction'] = {
        'involution': cm, 'inputs': S, 'orbit_representatives': reps,
        'W_naive_symmetric': W_naive, 'W_selftext_2k_plus_1': W_self,
        'OPT_RC_bruteforce': opt, 'OPT_witness': witness,
        'meaning': 'naive equivariant counts have W<OPT_RC, so no same-budget equivariant connection of them plus half-Euler can exist; the 2k+1 rule raises W'}
    assert W_naive == 6 and opt == 7 and W_self > W_naive and W_self <= 2 * opt

    # 2. r36 orientation instance: route 'min constrained cycle cover orientation + ordinary source'.
    cm3 = {'a': 'a', 'b': 'b', 'c': 'c'}
    rho3 = rho_of(cm3)
    S36 = ['cabbbca', 'aaccbb', 'cbacbca', 'bbacbb']
    rows, opt36, cmin, mins = analyse_orientations(S36, rho3, 'abc')
    out['r36_instance'] = {'inputs': S36, 'OPT_RC': opt36, 'min_constrained_CC': cmin,
                           'min_CC_orientations': mins,
                           'max_W_over_min_CC_orientations': max(r['W'] for r in mins)}

    # 3. Bounded seeded probe of the same alternative route on random instances.
    rng = random.Random(20261017)
    maps = [{'a': 'a', 'b': 'b'}, {'a': 'b', 'b': 'a'}, {'a': 'a', 'b': 'b', 'c': 'c'}, {'a': 'b', 'b': 'a', 'c': 'c'}]
    tested = 0
    some_minCC_W_gt_opt = []
    all_minCC_W_gt_opt = []
    attempts = 0
    while tested < 400 and attempts < 20000:
        attempts += 1
        cmx = rng.choice(maps)
        rx = rho_of(cmx)
        alpha = ''.join(sorted(cmx))
        n = rng.randrange(2, 5)
        words = [''.join(rng.choice(alpha) for _ in range(rng.randrange(3, 8))) for _ in range(n)]
        reps = reduce_rc(words, rx)
        if len(reps) < 2:
            continue
        both = reps + [rx(r) for r in reps if rx(r) != r]
        if not substring_free(both):
            continue
        tested += 1
        rows, o, c, mn = analyse_orientations(reps, rx, alpha)
        ws = [r['W'] for r in mn]
        rec = {'cm': cmx, 'reps': reps, 'OPT_RC': o, 'Cmin': c, 'W_minCC': ws}
        if max(ws) > o:
            some_minCC_W_gt_opt.append(rec)
        if min(ws) > o:
            all_minCC_W_gt_opt.append(rec)
    brute = []
    for rec in some_minCC_W_gt_opt[:3]:
        rx = rho_of(rec['cm'])
        alpha = ''.join(sorted(rec['cm']))
        L, wit = opt_rc_bruteforce(rec['reps'], rx, alpha, rec['OPT_RC'])
        assert L == rec['OPT_RC']
        brute.append({'reps': rec['reps'], 'OPT_RC_exhaustive_words': L, 'witness': wit})
    out['alternative_route_probe'] = {
        'exhaustive_word_crosscheck': brute,
        'seed': 20261017, 'instances_tested': tested, 'attempts': attempts,
        'instances_where_some_minCC_orientation_has_W_gt_OPT_RC': len(some_minCC_W_gt_opt),
        'instances_where_every_minCC_orientation_has_W_gt_OPT_RC': len(all_minCC_W_gt_opt),
        'first_examples_some': some_minCC_W_gt_opt[:3],
        'first_examples_all': all_minCC_W_gt_opt[:3],
        'meaning': 'bounded probe only; a zero count is not evidence that the route works'}
    out['scope_limit'] = 'finite diagnostics; no proof of the candidate, of the alternative route, or of novelty'
    return out


if __name__ == '__main__':
    result = main()
    text = json.dumps(result, indent=1, sort_keys=True) + '\n'
    if '--compare' in sys.argv:
        path = sys.argv[sys.argv.index('--compare') + 1]
        with open(path) as fh:
            saved = fh.read()
        if saved != text:
            print('MISMATCH', file=sys.stderr)
            sys.exit(1)
        print('MATCH')
    else:
        sys.stdout.write(text)
