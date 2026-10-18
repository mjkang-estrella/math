#!/usr/bin/env python3
"""MIT. Reviewer-written independent checks for the T025O54 proof review, round 1.
Usage: independent-checks.py /abs/fresh-arithmetic-discovery-r54 /abs/openai-proof-research
Read-only on both inputs. The author-verifier replay works on a copy in a fresh /var/tmp
directory that is removed on exit. Output: one JSON document on stdout.
Everything here is byte identity or a finite illustration. None of it proves an asymptotic
statement; the proof verdict rests on the written review only.
"""
import hashlib, json, math, random, shutil, subprocess, sys, tempfile
from fractions import Fraction as F
from pathlib import Path

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
FAMILY = 'preprints/Short-Egyptian-fractions-September-25-2026'
AUTHOR_ANCHORS = {
    'manifest.json': 'e32e49cd36807d4c18291bb60d45f6431e48fb0c61566bfcc6ca4f30a4c3ddd3',
    'scope-status.md': 'f6da553993dc03592a52711922035d412ca21b6840194fb4b3440e8e7415e0b6',
    'candidate-proof.md': '74217f39dd39087e9881c78048bf5ec1822218f4da997089feb36142265a9ef7',
    'constrained-descent.md': '4cdab2ae581fb42e4db335c41db32e797285c91fcf7669535e1900eded11a636',
    'contribution-comparison.md': '2282e8107869ac40d9393a328ab3f2ff64e85cb89f209ae02b65e80ca3adbac7',
    'reading-limits.md': 'a78dca74d4d00b5bd8c5bf3e803f90ec789e28ed751331a45a248568685cba43',
    'alternative-route.md': '829fe320bb5e293ee22325373b667fbcec9489f637491b07c31491c9e873e932',
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def git_blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def need(cond, msg):
    if not cond:
        raise SystemExit('CHECK FAILED: ' + msg)


def identities(packet, repo):
    out = {}
    for n, h in AUTHOR_ANCHORS.items():
        need(sha((packet / n).read_bytes()) == h, 'author anchor ' + n)
    out['author_anchors'] = 'PASS_7'
    tp = repo / 'sources/preprints-tree.json'
    raw = tp.read_bytes()
    need(sha(raw) == TREE_SHA, 'repository tree anchor')
    tree = json.loads(raw)
    need(tree['truncated'] is False and len(tree['tree']) == 13223, 'tree completeness')
    need(json.loads((repo / 'sources/upstream.json').read_text())['commit'] == PIN, 'pin')
    blobs = {e['path']: e['sha'] for e in tree['tree']
             if e['path'].startswith(FAMILY + '/') and e['type'] == 'blob'
             and not e['path'].lower().endswith('.pdf')}
    need(len(blobs) == 12, 'family non-PDF blob count')
    for path, gsha in sorted(blobs.items()):
        rel = path[len(FAMILY) + 1:]
        b = (packet / 'private/source025' / rel).read_bytes()
        need(git_blob(b) == gsha, 'source blob ' + rel)
    out['source025_blobs_vs_repository_tree'] = 'PASS_12'
    return out


def constants():
    K, R, D0, eta = 100, 1000, 100000, F(1, 10000)
    DM = (2 * R + 2) * (K + 2); DX = DM + 2; DC = 4 * DX
    c = {
        '(2R+1)K<DM': (2 * R + 1) * K < DM,
        'gcd_slack .08(K-4)/(K+1)>.05': F(8, 100) * (K - 4) / (K + 1) > F(5, 100),
        'fresh product exponent .75(K+1)/K<.9': F(75, 100) * (K + 1) / K < F(9, 10),
        'atom exponent .74(K-2)/K>=.7': F(74, 100) * (K - 2) / K >= F(7, 10),
        'bilinear 1/2-2*.35<=-.2': F(1, 2) - 2 * F(35, 100) <= F(-2, 10),
        'high/middle Markov 10eta-.01(1-eta)<-.008': 10 * eta - F(1, 100) * (1 - eta) < F(-8, 1000),
        'terminal 4eta+3/D0<.005': 4 * eta + F(3, D0) < F(5, 1000),
        'terminal block 10eta-.01+6/D0<-.008': 10 * eta - F(1, 100) + F(6, D0) < F(-8, 1000),
        'U^4<=e^(DC S) at U<=e^(DX S)': 4 * DX <= DC,
        'upper phase (1.6DC+K+2)<=.8*3DC': F(16, 10) * DC + K + 2 <= F(8, 10) * 3 * DC,
        'lower phase 1.4DC>DC (pays 2ell)': F(14, 10) * DC > DC,
        'C>X_0: 1.4DC>DX': F(14, 10) * DC > DX,
        'merge DX-DM-1=1': DX - DM - 1 == 1,
        '2s<=m/4 at V<=2S: 2*.75*2/K<1/4': 2 * F(75, 100) * 2 / K < F(1, 4),
        'prefix S range: 2DC/1.5DC=4/3 and 4DC/1.5DC=8/3': (F(2, 1) / F(3, 2), F(4, 1) / F(3, 2)) == (F(4, 3), F(8, 3)),
    }
    need(all(c.values()), 'constant slack ' + str([k for k, v in c.items() if not v]))
    return {'DM': DM, 'DX': DX, 'DC': DC, 'checks': {k: bool(v) for k, v in c.items()}}


TEMPL = {1: [7], 2: [7, 9, 33, 693], 3: [3, 11, 231], 4: [3, 7, 11, 231]}


def factor_primes(n):
    ps, p = set(), 2
    while p * p <= n:
        while n % p == 0:
            ps.add(p); n //= p
        p += 1
    if n > 1:
        ps.add(n)
    return ps


def templates():
    for d, L in TEMPL.items():
        need(sum(F(1, x) for x in L) == F(d, 7), 'template sum %d' % d)
        need(len(set(L)) == len(L) and all(x % 2 and x % 5 for x in L), 'template shape %d' % d)
        need(set().union(*[factor_primes(x) for x in L]) <= {3, 7, 11}, 'template support %d' % d)
    return 'PASS_4_TEMPLATES'


def digit_expansion(u, a, M0, ell, nu):
    out, j = [], 0
    while u:
        bj = u % 5
        if bj:
            mult = ell ** nu * M0 // (7 * 5 ** j)
            need(mult * 7 * 5 ** j == ell ** nu * M0, 'multiplier integrality')
            out += [x * mult for x in TEMPL[bj]]
        u //= 5; j += 1
    need(j <= a + 1, 'digit range')
    return out


def vp(n, p):
    k = 0
    while n % p == 0:
        n //= p; k += 1
    return k


def toy_merge():
    """Independent toy of the final merge using only digit expansions (no asymptotics)."""
    a, ell, extra = 5, 17, 19
    M0 = 7 * 5 ** a * extra
    checked = 0
    for n in range(2, 900, 7):
        for g in (1, 3, 17, 51, 289):
            for u in range(1, n):
                v = n - u
                if u > 5 ** a or ell * v > 5 ** a:
                    continue
                L0 = digit_expansion(u, a, M0, ell, 0)
                L1 = digit_expansion(ell * v, a, M0, ell, 1)
                need(all(vp(x, ell) == 0 for x in L0) and all(vp(x, ell) == 1 for x in L1), 'valuation')
                tot = [x * g for x in L0 + L1]
                need(len(set(tot)) == len(tot), 'distinct after g')
                need(all(x % 2 for x in tot), 'odd')
                need(sum(F(1, x) for x in tot) == F(n, M0 * g), 'sum')
                checked += 1
    return {'instances': checked, 'ell': ell, 'a': a, 'M0': M0, 'g_values_include_ell_multiples': True}


def constrained_step(seed=20261018):
    rnd = random.Random(seed)
    n = 0
    for _ in range(20000):
        ell = rnd.choice([13, 17, 19, 23, 29])
        u = rnd.randint(2, 4000)
        Q = rnd.choice([1, 2 * rnd.randint(0, 50) + 1])
        t = rnd.randint(1, 5000)
        delta = F(rnd.randint(1, 99), 100)
        x = F(Q * t, 2 * ell * u)
        frac = x - (x.numerator // x.denominator)
        in_J = F(1, 2 * ell) - delta / (2 * ell) < frac <= F(1, 2 * ell)
        k = x.numerator // x.denominator
        z = 1 + 2 * ell * k
        h = u * z - Q * t
        good_canonical = 0 <= h < delta * u
        brute = any(0 <= u * zz - Q * t < delta * u for zz in range(1, Q * t // u + 4 * ell + 3, 2 * ell))
        need(in_J == good_canonical == brute, 'interval equivalence')
        if good_canonical:
            nu, M0 = rnd.choice([0, 1]), t * rnd.choice([1, 3, 5, 7])
            lhs = F(u, ell ** nu * M0 * Q)
            rhs = F(1, (ell ** nu * M0 // t) * z) + F(h, ell ** nu * M0 * Q * z)
            need(lhs == rhs, 'step identity')
            need(z % 2 == 1 and z % ell == 1, 'z odd, ell-free')
            if Q * t > u:
                need(F(h, ell ** nu * M0 * Q * z) < F(1, (ell ** nu * M0 // t) * z), 'residual below first term')
            n += 1
    return {'trials': 20000, 'successful_steps_checked': n}


def odd_prefix(seed=7, D=3):
    """Reviewer reimplementation of the odd harmonic prefix and odd greedy steps (T=b^(2D), small D)."""
    rnd = random.Random(seed)
    worst = 0.0
    for _ in range(3000):
        b = 2 * rnd.randint(1, 10 ** rnd.randint(1, 25)) + 1
        a = rnd.randint(1, b - 1)
        A, C, dens = a, b, []
        d = 3
        while A and d * A >= C:
            dens.append(d); A, C = d * A - C, d * C; d += 2
        need(len(dens) <= 6, 'harmonic prefix length')
        T = b ** (2 * D)
        A0, j = A, 0
        while A and C < T:
            nn = -(-C // A)
            if nn % 2 == 0:
                nn += 1
            need(not dens or nn > dens[-1], 'strict increase')
            A2, C2 = nn * A - C, nn * C
            need(A2 < 2 * A and C2 <= C * (C + 2), 'numerator/denominator recursion')
            need(F(A2, C2) < F(1, nn), 'remainder below last reciprocal')
            dens.append(nn); A, C = A2, C2; j += 1
        need(sum(F(1, x) for x in dens) + F(A, C) == F(a, b), 'telescoping')
        need(all(x % 2 for x in dens) and C % 2, 'oddness')
        need(j <= math.log2(math.log(T) / math.log(1.5)) + 1, 'step bound')
        if A:
            need(T <= C < T * T + 2 * T, 'crossing range')
            need(A <= 45045 * b * 2 ** j, 'numerator bound')
            need(all(F(A, C) < F(1, x) for x in dens), 'remainder below every prefix reciprocal')
            worst = max(worst, j / max(1.0, math.log2(math.log(b))))
    return {'pairs': 3000, 'D_used': D, 'max_steps_over_log2loglogb': round(worst, 3)}


def obstruction():
    """k<=3 odd expansions (repetitions allowed) of (b+1)/(2b): check b<=P_j<=(2k)^(2^j-1)."""
    found, BMAX = [], 20001
    for b in range(3, BMAX + 1, 2):
        target = F(b + 1, 2 * b)
        for x in range(3, 8, 2):
            r1 = target - F(1, x)
            if r1 <= 0:
                continue
            if r1.numerator == 1 and r1.denominator % 2 and r1.denominator >= x:
                found.append((b, [x, r1.denominator]))
            y = x
            while F(2, y) >= r1:
                r2 = r1 - F(1, y)
                if r2 > 0 and r2.numerator == 1 and r2.denominator % 2 and r2.denominator >= y:
                    found.append((b, [x, y, r2.denominator]))
                y += 2
    need(found, 'no small expansions found')
    for b, dl in found:
        k = len(dl); P = 1; part = F(0)
        for i, di in enumerate(dl, 1):
            need(di <= 2 * k * P, 'd_i<=2kP_{i-1}')
            P *= di; part += F(1, di)
            need(P <= (2 * k) ** (2 ** i - 1), 'P_i bound')
            if part > F(1, 2):
                need(b <= P, 'b<=P_j'); break
    return {'expansions_found': len(found), 'max_b': max(b for b, _ in found), 'bound_k2': 4 ** 3, 'bound_k3': 6 ** 7}


def author_replay(packet):
    scratch = Path(tempfile.mkdtemp(prefix='t025o-proof-r1-replay-', dir='/var/tmp'))
    try:
        res = {}
        for name in ('positive', 'wrong_anchor', 'payload_mutation'):
            cp = scratch / name / 'packet'
            shutil.copytree(packet, cp, symlinks=True)
            anchor = AUTHOR_ANCHORS['manifest.json']
            if name == 'wrong_anchor':
                anchor = '0' * 64
            if name == 'payload_mutation':
                with (cp / 'candidate-proof.md').open('a') as f:
                    f.write('\nmutation\n')
            r = subprocess.run([sys.executable, '-B', str(cp / 'verify.py'), anchor], capture_output=True, text=True, cwd='/')
            res[name] = {'returncode': r.returncode, 'output': (r.stdout + r.stderr).strip()}
        need(res['positive']['returncode'] == 0 and 'PASS_EXACT_INVENTORY' in res['positive']['output'], 'author positive')
        need(res['wrong_anchor']['returncode'] != 0 and 'anchor mismatch' in res['wrong_anchor']['output'], 'author wrong anchor')
        need(res['payload_mutation']['returncode'] != 0 and 'file inventory mismatch' in res['payload_mutation']['output'], 'author payload')
        return res
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


def main(packet, repo):
    packet, repo = Path(packet), Path(repo)
    need(packet.is_absolute() and repo.is_absolute(), 'absolute paths required')
    out = {
        'identities': identities(packet, repo),
        'constants': constants(),
        'templates': templates(),
        'toy_merge': toy_merge(),
        'constrained_step': constrained_step(),
        'odd_prefix': odd_prefix(),
        'obstruction_small_k': obstruction(),
        'author_verifier_replay': author_replay(packet),
        'limits': 'Byte identities and finite illustrations only; not evidence for any asymptotic claim.',
    }
    out['status'] = 'PASS_INDEPENDENT_CHECKS'
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit('usage: independent-checks.py /abs/packet /abs/repo')
    main(sys.argv[1], sys.argv[2])
