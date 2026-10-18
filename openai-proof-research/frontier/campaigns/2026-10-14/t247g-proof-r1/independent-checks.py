#!/usr/bin/env python3
"""MIT. T247G proof-r1 independent read-only checks (standard library only).

Usage: independent-checks.py AUTHOR_PACKET_DIR REPO_ROOT

Part A re-derives Git blob identities of all 31 retained source bodies from
REPO_ROOT/sources/preprints-tree.json, whose SHA256 is fixed below from the
dispatch, and checks the three operative files against dispatch hashes.
Parts B-D are finite illustrations chosen by the reviewer, distinct from the
author's diagnostics. Nothing is written. None of this proves the compiler
delta, the orbit partition or the universal theorem.
"""
import hashlib, json, random, sys
from itertools import permutations, product
from math import ceil, log2
from pathlib import Path

TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
P = 'preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/build/sections/'
Q = 'preprints/An-infinite-finitely-presented-residually-finite-2-group-October-5-2026/build/sections/'
OPERATIVE = {
    P + 'finite-rules.tex': ('7ba23dba6390e947e121c2d86dffc3cbf6a636f0',
                             'ab12219e94a9bf440c119f21768c6706b3d3be703bcfd6ade1244d5fb9ecdace'),
    P + 'cancellation.tex': ('b52ff630b3a50878ee59f3d7a0e3cf70d0d38bdb',
                             '105759c220c6c048c888273302ffab5811a409b7d90a09bbfc8211c67638ef1c'),
    Q + 'ring-phases.tex': ('3efd117f158209e3365fc4d953b6bb64aa53d9d7', None),
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def git_blob(b):
    return hashlib.sha1(b'blob %d\0' % len(b) + b).hexdigest()


def part_a(packet, repo):
    raw = (repo / 'sources/preprints-tree.json').read_bytes()
    assert sha(raw) == TREE_SHA256, 'preprints-tree anchor mismatch'
    t = json.loads(raw)
    assert t['truncated'] is False
    tree = {e['path']: e for e in t['tree']}
    receipts = json.loads((packet / 'all-source-receipts.json').read_text())
    assert len(receipts) == 31
    matched, operative = 0, {}
    for e in receipts:
        b = (packet / e['local']).read_bytes()
        g = git_blob(b)
        key = e['path'] if e['path'] in tree else e['path'].removeprefix('preprints/')
        te = tree.get(key)
        assert te is not None and te['type'] == 'blob' and te['sha'] == g, 'tree mismatch: ' + e['path']
        matched += 1
        if e['path'] in OPERATIVE:
            want_git, want_sha = OPERATIVE[e['path']]
            assert g == want_git and (want_sha is None or sha(b) == want_sha), 'operative mismatch'
            operative[e['path']] = {'git_blob_sha1': g, 'sha256': sha(b), 'newline_count': b.count(b'\n')}
    assert len(operative) == 3
    return {'tree_entries': len(tree), 'truncated': False, 'blobs_matched': matched, 'operative': operative}


# --- Part B: alternation in a non-closed subspace of a noncommutative algebra ---
# 3x3 matrices over F2 encoded as 9-bit integers.
def mmul(a, b):
    r = 0
    for i in range(3):
        for j in range(3):
            z = 0
            for k in range(3):
                z ^= ((a >> (3 * i + k)) & 1) & ((b >> (3 * k + j)) & 1)
            r |= z << (3 * i + j)
    return r


ID3 = sum(1 << (4 * i) for i in range(3))


def alt(xs):
    r = 0
    for perm in permutations(range(len(xs))):
        v = ID3
        for i in perm:
            v = mmul(v, xs[i])
        r ^= v
    return r


def span(basis):
    s = {0}
    for b in basis:
        s |= {x ^ b for x in s}
    return s


def rank(vs):
    rows, r = list(vs), 0
    for bit in range(9):
        piv = next((i for i in range(r, len(rows)) if rows[i] >> bit & 1), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i] >> bit & 1:
                rows[i] ^= rows[r]
        r += 1
    return r


def part_b():
    rng = random.Random(247)
    out = []
    for e in (2, 3):
        while True:
            basis = [rng.randrange(1, 512) for _ in range(e)]
            if rank(basis) != e:
                continue
            E = span(basis)
            closed = all(mmul(x, y) in E for x in E for y in E)
            noncomm = any(mmul(x, y) != mmul(y, x) for x in E for y in E)
            if not closed and noncomm:
                break
        Es = sorted(E)
        tested = 0
        for xs in product(Es, repeat=e + 1):
            assert alt(list(xs)) == 0
            tested += 1
        # threshold control: some e-tuple from E has nonzero alternation
        witness = next((xs for xs in product(Es, repeat=e) if alt(list(xs)) != 0), None)
        assert witness is not None
        # order control: exterior factors U,V stay outside: U*Alt*V == 0 for random U,V
        for _ in range(50):
            U, V = rng.randrange(512), rng.randrange(512)
            xs = [rng.choice(Es) for _ in range(e + 1)]
            assert mmul(mmul(U, alt(xs)), V) == 0
        out.append({'dim_E': e, 'E_closed_under_product': closed, 'E_noncommutative': noncomm,
                    'tuples_m_eq_dim_plus_1_all_zero': tested, 'nonzero_witness_at_m_eq_dim': True})
    return out


# --- Part C: exact height arithmetic for h_{j+1}=h_j^2 ---
def part_c():
    cases = 0
    for h0 in range(2, 41):
        hs = [h0]
        for j in range(1, 7):
            hs.append(hs[-1] ** 2)
            assert sum(hs[:-1]) <= 2 * hs[-2], (h0, j)
            assert hs[-2] ** 2 == hs[-1]
            cases += 1
    return {'pairs_h0_j_checked': cases, 'claim': 'sum_{i<j} h_i <= 2 h_{j-1} = 2 sqrt(h_j)'}


# --- Part D: certified stopping levels from the displayed bound (2) ---
def part_d():
    c, k = 10000, 10
    rows = []
    for (d, C, g, h0) in [(1, 1, 0, 2), (10 ** 6, 10 ** 9, 3.5, 2), (1, 1, 10 ** 9, 2), (7, 2, 50, 64)]:
        hs = [h0]
        for j in range(1, 12):
            hs.append(hs[-1] ** 2)
            # integer upper bound for log2 R_j via (2), rounding every log upward
            ub = (2 * ceil(log2(d)) + ceil(log2(C)) + ceil(g) + 2 * (j - 1) * ceil(log2(k))
                  + ceil(g) * j * ceil(log2(3 * k)) + 2 * k * c * sum(hs[1:j]) + ceil(g) * sum(hs[:j]))
            # need 2^{h_j} > 100k(R_j+3); suffices h_j > ub + log2(400k)
            if hs[j] > ub + ceil(log2(400 * k)):
                rows.append({'d': d, 'C': C, 'g': g, 'h0': h0, 'J': j,
                             'h_J_bits': hs[j].bit_length(), 'log2_R_upper_bits': ub.bit_length()})
                break
        else:
            raise AssertionError('no stop found')
    return rows


def main():
    if len(sys.argv) != 3:
        raise SystemExit('usage: independent-checks.py AUTHOR_PACKET_DIR REPO_ROOT')
    packet, repo = Path(sys.argv[1]).absolute(), Path(sys.argv[2]).absolute()
    print(json.dumps({'status': 'PASS_INDEPENDENT_FINITE_CHECKS',
                      'A_source_identity': part_a(packet, repo),
                      'B_alternation_noncommutative_nonclosed': part_b(),
                      'C_height_sums': part_c(),
                      'D_stopping_level_samples': part_d(),
                      'limits': 'Finite illustrations and byte identities only. Not evidence for the '
                                'compiler delta, orbit partition, cut identity or universal termination.'},
                     indent=1))


if __name__ == '__main__':
    main()
