"""Independent T314C proof-review checks (identity, integrity controls, finite diagnostics).

Reviewer code, written from scratch; it imports nothing from the author packet.
Identity checks certify byte identity and provenance only. Finite diagnostics
are exact computations on small instances; they do not prove the uniform
theorem and are not part of the proof verdict.

Usage (all modes require the externally supplied author MANIFEST.json SHA256):
    python -B review_check.py identity --expected HASH --packet DIR --tree TREE
    python -B review_check.py controls --expected HASH --packet DIR --tree TREE --scratch /var/tmp/...
    python -B review_check.py finite   --expected HASH --packet DIR --tree TREE
    python -B review_check.py review-identity --expected REVIEW_MANIFEST_SHA256
"""
import argparse, hashlib, itertools, json, os, random, re, shutil, subprocess, sys
from pathlib import Path

CANDIDATE_SHA = '7bc61c8a0949c671a5f8dd8b9f55502e1b526ed40968dc0912be984f789eaea9'
SCOPE_SHA = '676eed9172e85a2c99a7ff52dbe911cae036c104dba0bb409a2b158e4791f29e'
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
TREE_ENTRIES = 13223
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PREFIX = 'preprints/Cyclic-Length-and-Chromatic-Fixed-Point-Loss-September-24-2026/'
INTRO_BLOB = 'cb2ae4e2f83da44f5cf0cc4310e460d3240c2a6d'


class Reject(Exception):
    pass


def need(ok, reason):
    if not ok:
        raise Reject(reason)


def sha256(b):
    return hashlib.sha256(b).hexdigest()


def git_blob(b):
    return hashlib.sha1(b'blob %d\0' % len(b) + b).hexdigest()


# ---------------------------------------------------------------- identity

def identity(packet, expected, tree):
    need(isinstance(expected, str) and re.fullmatch('[0-9a-f]{64}', expected) is not None, 'EXPECTED_FORMAT')
    raw = (packet / 'MANIFEST.json').read_bytes()
    need(sha256(raw) == expected, 'MANIFEST_ANCHOR')
    m = json.loads(raw)
    entries = list(packet.rglob('*'))
    need(not any(e.is_symlink() for e in entries), 'SYMLINK')
    files = {str(e.relative_to(packet)) for e in entries if e.is_file()} - {'MANIFEST.json'}
    need(files == set(m['files']), 'MEMBERSHIP')
    dirs = sorted(str(e.relative_to(packet)) for e in entries if e.is_dir())
    need(dirs == sorted(m['directories']), 'DIRECTORIES')
    for f, h in m['files'].items():
        need(not Path(f).is_absolute() and '..' not in Path(f).parts, 'UNSAFE_PATH')
        need(sha256((packet / f).read_bytes()) == h, 'PAYLOAD_HASH')
    need(sha256((packet / 'candidate.md').read_bytes()) == CANDIDATE_SHA, 'CANDIDATE_ANCHOR')
    need(sha256((packet / 'original-scope.md').read_bytes()) == SCOPE_SHA, 'SCOPE_ANCHOR')
    tb = tree.read_bytes()
    need(sha256(tb) == TREE_SHA, 'TREE_ANCHOR')
    t = json.loads(tb)
    need(t.get('truncated') is False and len(t['tree']) == TREE_ENTRIES, 'TREE_SHAPE')
    canon = {e['path']: e for e in t['tree']}
    need(len(canon) == TREE_ENTRIES, 'TREE_UNIQUE')
    receipts = json.loads((packet / 'source-receipts.json').read_bytes())
    wanted = {e['path'] for e in t['tree'] if e['type'] == 'blob' and e['path'].startswith(PREFIX)
              and not e['path'].endswith('.pdf')}
    need({r['path'] for r in receipts} == wanted and len(receipts) == 12, 'SOURCE_MEMBERSHIP')
    for r in receipts:
        need(r['path'].startswith('preprints/'), 'SOURCE_PREFIX')
        need(r['url'] == f'https://raw.githubusercontent.com/openai/math/{PIN}/{r["path"]}', 'SOURCE_URL')
        b = (packet / r['copy']).read_bytes()
        g = git_blob(b)
        need(g == canon[r['path']]['sha'] and g == r['git_blob'], 'SOURCE_BLOB')
        need(canon[r['path']].get('size') == len(b), 'SOURCE_SIZE')
        need(sha256(b) == r['sha256'], 'SOURCE_SHA')
    intro = [r for r in receipts if r['path'].endswith('01-introduction.tex')][0]
    need(intro['git_blob'] == INTRO_BLOB, 'INTRO_BLOB')
    body = (packet / intro['copy']).read_text()
    need('\\label{thm:main}' in body and '\\boxed{r_n(G,H)=\\ell(G,H).}' in body
         and 'finite spectra include compact retracts' in body and 'K(0)=H\\Q' in body, 'THM_MAIN_TEXT')
    return {'identity': 'verified', 'payloads': len(files), 'source_blobs': len(receipts),
            'limits': 'byte identity/provenance only'}


# ---------------------------------------------------------------- controls

def run_identity_subprocess(packet, expected, tree):
    r = subprocess.run([sys.executable, '-B', __file__, 'identity', '--expected', expected,
                        '--packet', str(packet), '--tree', str(tree)], capture_output=True, text=True)
    return r.returncode, r.stdout.strip()


def reseal(packet):
    mp = packet / 'MANIFEST.json'
    m = json.loads(mp.read_bytes())
    m['files'] = {f: sha256((packet / f).read_bytes()) for f in m['files']}
    b = json.dumps(m, indent=2).encode()
    mp.write_bytes(b)
    return sha256(b)


def flip(path):
    b = bytearray(path.read_bytes())
    b[len(b) // 2] ^= 1
    path.write_bytes(bytes(b))


def controls(packet, expected, tree, scratch):
    identity(packet, expected, tree)  # trust nothing before the anchor verifies
    scratch.mkdir(parents=True, exist_ok=True)
    out = []
    rc, s = run_identity_subprocess(packet, expected, tree)
    need(rc == 0 and json.loads(s)['identity'] == 'verified', 'POSITIVE_BASELINE')
    out.append({'control': 'positive-baseline', 'result': 'accepted'})

    def trial(name, reason, mutate):
        p = scratch / name
        if p.exists():
            shutil.rmtree(p)
        shutil.copytree(packet, p, symlinks=True)
        tr = scratch / (name + '-tree.json')
        shutil.copyfile(tree, tr)
        exp = mutate(p, tr) or expected
        rc, s = run_identity_subprocess(p, exp, tr)
        need(rc != 0 and s == 'REJECT: ' + reason, 'CONTROL_' + name + ':' + s)
        out.append({'control': name, 'rejection': reason})
        shutil.rmtree(p)
        tr.unlink()

    trial('wrong-anchor', 'MANIFEST_ANCHOR', lambda p, t: '0' * 64)
    trial('malformed-anchor', 'EXPECTED_FORMAT', lambda p, t: 'abc')
    trial('candidate-flip', 'PAYLOAD_HASH', lambda p, t: flip(p / 'candidate.md'))
    trial('candidate-flip-resealed', 'CANDIDATE_ANCHOR', lambda p, t: (flip(p / 'candidate.md'), reseal(p))[1])
    trial('scope-flip-resealed', 'SCOPE_ANCHOR', lambda p, t: (flip(p / 'original-scope.md'), reseal(p))[1])
    trial('extra-file', 'MEMBERSHIP', lambda p, t: (p / 'extra.md').write_text('x') and None)
    trial('missing-file', 'MEMBERSHIP', lambda p, t: (p / 'comparison.md').unlink())
    trial('symlink', 'SYMLINK', lambda p, t: os.symlink('candidate.md', p / 'link.md'))
    trial('tree-flip', 'TREE_ANCHOR', lambda p, t: flip(t))

    def source_mut(p, t):
        f = p / 'private/build/sections/01-introduction.tex'
        f.write_bytes(f.read_bytes().replace(b'r_n(G,H)=\\ell(G,H)', b'r_n(G,H)\\le\\ell(G,H)'))
        rp = p / 'source-receipts.json'
        r = json.loads(rp.read_bytes())
        for e in r:
            if e['copy'] == 'private/build/sections/01-introduction.tex':
                e['sha256'] = sha256(f.read_bytes())
        rp.write_bytes(json.dumps(r, indent=2).encode())
        return reseal(p)
    trial('source-theorem-edit-resealed', 'SOURCE_BLOB', source_mut)

    def receipt_mut(p, t):
        rp = p / 'source-receipts.json'
        r = json.loads(rp.read_bytes())
        r[0]['url'] = r[0]['url'].replace(PIN, 'main')
        rp.write_bytes(json.dumps(r, indent=2).encode())
        return reseal(p)
    trial('unpinned-url-resealed', 'SOURCE_URL', receipt_mut)

    def drop_receipt(p, t):
        rp = p / 'source-receipts.json'
        r = json.loads(rp.read_bytes())[1:]
        rp.write_bytes(json.dumps(r, indent=2).encode())
        return reseal(p)
    trial('dropped-source-resealed', 'SOURCE_MEMBERSHIP', drop_receipt)
    return out


# ---------------------------------------------------------------- finite algebra

def poly_irreducible(p, d):
    for coeffs in itertools.product(range(p), repeat=d):
        f = list(coeffs) + [1]  # monic, low degree first
        if f[0] == 0:
            continue
        if all(sum(f[i] * pow(x, i, p) for i in range(d + 1)) % p for x in range(p)) and d <= 3:
            return f
        if d > 3:
            raise NotImplementedError
    raise ValueError


def field(p, d):
    f = poly_irreducible(p, d)

    def mul(a, b):
        r = [0] * (2 * d - 1)
        for i in range(d):
            for j in range(d):
                r[i + j] = (r[i + j] + a[i] * b[j]) % p
        for k in range(2 * d - 2, d - 1, -1):
            c = r[k]
            if c:
                for i in range(d + 1):
                    r[k - d + i] = (r[k - d + i] - c * f[i]) % p
        return tuple(r[:d])

    def pw(a, e):
        r = tuple([1] + [0] * (d - 1))
        for _ in range(e):
            r = mul(r, a)
        return r
    return mul, pw


def beta_gq(p, d):
    mul, pw = field(p, d)

    def beta(x, y):
        a = mul(x, pw(y, p))
        b = mul(pw(x, p), y)
        return tuple((u - v) % p for u, v in zip(a, b))
    return beta


def beta_from_constants(p, d, consts):
    def beta(x, y):
        out = [0] * d
        for (i, j), v in consts.items():
            c = (x[i] * y[j] - x[j] * y[i]) % p
            if c:
                for k in range(d):
                    out[k] = (out[k] + c * v[k]) % p
        return tuple(out)
    return beta


def rank_mod_p(rows, p):
    rows = [list(r) for r in rows]
    rk, col, n = 0, 0, len(rows[0]) if rows else 0
    while rk < len(rows) and col < n:
        piv = next((i for i in range(rk, len(rows)) if rows[i][col] % p), None)
        if piv is None:
            col += 1
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][col], p - 2, p)
        rows[rk] = [v * inv % p for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col]:
                c = rows[i][col]
                rows[i] = [(a - c * b) % p for a, b in zip(rows[i], rows[rk])]
        rk += 1
        col += 1
    return rk


def rho(p, d, beta):
    basis = [tuple(1 if k == i else 0 for k in range(d)) for i in range(d)]
    best = None
    ranks = []
    for f in itertools.product(range(p), repeat=d):
        if not any(f):
            continue
        M = [[sum(fk * bk for fk, bk in zip(f, beta(basis[i], basis[j]))) % p for j in range(d)] for i in range(d)]
        r = rank_mod_p(M, p)
        ranks.append(r)
        best = r if best is None else min(best, r)
    return best // 2, sorted(set(ranks))


class Group:
    """Black-box group on (Z/p^2)^d with the candidate's multiplication (or a mutation)."""

    def __init__(self, p, d, corr):
        self.p, self.d, self.q = p, d, p * p
        self.n = self.q ** d
        self.vec = [tuple((x // self.q ** k) % self.q for k in range(d)) for x in range(self.n)]
        half = (p + 1) // 2
        T = []
        for x in range(self.n):
            vx = self.vec[x]
            row = []
            for y in range(self.n):
                vy = self.vec[y]
                c = corr(tuple(a % p for a in vx), tuple(b % p for b in vy))
                s = [(vx[k] + vy[k] + p * (half * c[k] % p)) % self.q for k in range(d)]
                row.append(sum(s[k] * self.q ** k for k in range(d)))
            T.append(row)
        self.T = T
        self.e = 0
        self.inv = [next(y for y in range(self.n) if T[x][y] == 0) for x in range(self.n)]
        self.pw = []
        for x in range(self.n):
            g = 0
            for _ in range(p):
                g = T[g][x]
            self.pw.append(g)

    def assoc_sample(self, trials, seed):
        rnd = random.Random(seed)
        T = self.T
        for _ in range(trials):
            a, b, c = (rnd.randrange(self.n) for _ in range(3))
            if T[T[a][b]][c] != T[a][T[b][c]]:
                return False
        return True

    def bar(self, x):
        return tuple(v % self.p for v in self.vec[x])


def cocycle_exhaustive(p, d, corr):
    L = list(itertools.product(range(p), repeat=d))
    add = lambda u, v: tuple((a + b) % p for a, b in zip(u, v))
    for x in L:
        for y in L:
            cxy = corr(x, y)
            xy = add(x, y)
            for z in L:
                if add(cxy, corr(xy, z)) != add(corr(y, z), corr(x, add(y, z))):
                    return False
    return True


def members(mask):
    out, i = [], 0
    while mask:
        if mask & 1:
            out.append(i)
        mask >>= 1
        i += 1
    return out


def subgroups(G):
    """All subgroups, by adjoining g normalizing M with g^p in M (complete for p-groups)."""
    T, p = G.T, G.p
    levels = [{1 << 0}]
    norm = {}
    while True:
        nxt = set()
        for M in levels[-1]:
            mem = members(M)
            N = 0
            for g in range(G.n):
                gi = G.inv[g]
                row = T[g]
                if all((M >> T[row[k]][gi]) & 1 for k in mem):
                    N |= 1 << g
            norm[M] = N
            for g in members(N & ~M):
                if not (M >> G.pw[g]) & 1:
                    continue
                H, gk = M, 0
                for _ in range(p - 1):
                    gk = T[gk][g]
                    for k in mem:
                        H |= 1 << T[gk][k]
                nxt.add(H)
        if not nxt:
            break
        levels.append(nxt)
    allsg = [H for lev in levels for H in lev]
    return levels, norm, allsg


def cyclic_length(G, levels, norm, allowed=None, ignore_cyclic=False, global_normal=False):
    """Exact minimum length of a strict subnormal chain 1=H0<...<Hk=G with cyclic factors."""
    p = G.p
    full = (1 << G.n) - 1
    ell, back = {1: 0}, {1: None}
    powers = {}
    for k in range(1, len(levels)):
        for H in levels[k]:
            if allowed is not None and H not in allowed:
                continue
            P = 0
            for h in members(H):
                P |= 1 << G.pw[h]
            powers[H] = P
            best = None
            for j in (k - 1, k - 2):
                if j < 0:
                    continue
                for K in levels[j]:
                    if K not in ell or K & ~H:
                        continue
                    if H & ~norm[K]:
                        continue  # K not normal in H
                    if global_normal and full & ~norm[K]:
                        continue
                    if j == k - 2 and not ignore_cyclic and not (P & ~K):
                        continue  # index p^2 but every h^p in K: quotient elementary, not cyclic
                    if best is None or ell[K] + 1 < best[0]:
                        best = (ell[K] + 1, K)
            if best is not None:
                ell[H], back[H] = best
    top = max(levels[-1])
    chain, H = [], top
    while H is not None:
        chain.append(H)
        H = back[H]
    return ell.get(top), chain[::-1]


def verify_chain(G, chain):
    """Re-verify an explicit chain step by step from the multiplication table alone."""
    T = G.T
    need(chain[0] == 1 and chain[-1] == (1 << G.n) - 1, 'CHAIN_ENDS')
    for K, H in zip(chain, chain[1:]):
        km, hm = members(K), members(H)
        need(not (K & ~H) and K != H, 'CHAIN_STRICT')
        for h in hm:
            for k in km:
                need((K >> T[T[h][k]][G.inv[h]]) & 1, 'CHAIN_NORMAL')
        idx = len(hm) // len(km)
        gen = None
        for h in hm:
            cos, g = set(), 0
            for _ in range(idx):
                cos.add(min(T[g][k] for k in km))
                g = T[g][h]
            if len(cos) == idx:
                gen = h
                break
        need(gen is not None, 'CHAIN_CYCLIC')
    return True


def proof_invariants(G, beta, levels, norm):
    """On every cyclic order-p^2 edge K<|H: dim U_H = dim U_K + 1 and beta(U_H,U_H) in W_K."""
    p, d = G.p, G.d
    checked = 0
    for k in range(2, len(levels)):
        for H in levels[k]:
            hm = members(H)
            UH = {G.bar(h) for h in hm}
            P = 0
            for h in hm:
                P |= 1 << G.pw[h]
            for K in levels[k - 2]:
                if K & ~H or H & ~norm[K] or not (P & ~K):
                    continue
                km = members(K)
                UK = {G.bar(x) for x in km}
                need(len(UH) == p * len(UK), 'U_JUMP')
                WK = {tuple(v // p for v in G.vec[z]) for z in km if G.bar(z) == (0,) * d}
                for u in UH:
                    for v in UH:
                        need(beta(u, v) in WK, 'ISOTROPY')
                checked += 1
    return checked


def finite(packet, expected, tree):
    identity(packet, expected, tree)
    res = []
    rnd = random.Random(20261018)
    p = 3
    cases = [('gq-p3-d3', 3, 3, beta_gq(3, 3)), ('zero-p3-d3', 3, 3, beta_from_constants(3, 3, {}))]
    for t in range(3):
        consts = {(i, j): tuple(rnd.randrange(3) for _ in range(3)) for i in range(3) for j in range(i + 1, 3)}
        cases.append((f'random{t}-p3-d3', 3, 3, beta_from_constants(3, 3, consts)))
    for t in range(2):
        consts = {(0, 1): tuple(rnd.randrange(5) for _ in range(2))}
        cases.append((f'random{t}-p5-d2', 5, 2, beta_from_constants(5, 2, consts)))
    for name, p, d, raw_beta in cases:
        cache = {}

        def beta(x, y, raw_beta=raw_beta, cache=cache):
            if (x, y) not in cache:
                cache[(x, y)] = raw_beta(x, y)
            return cache[(x, y)]
        need(cocycle_exhaustive(p, d, beta), 'COCYCLE_' + name)
        G = Group(p, d, beta)
        need(G.assoc_sample(20000, 1), 'ASSOC_' + name)
        # commutator and power identities, all pairs (x y x^-1 y^-1 convention)
        for x in range(G.n):
            need(G.pw[x] == sum((p * (v % p) % G.q) * G.q ** k for k, v in enumerate(G.vec[x])), 'POWER_' + name)
        for x in range(G.n):
            for y in range(G.n):
                c = G.T[G.T[G.T[x][y]][G.inv[x]]][G.inv[y]]
                b = beta(G.bar(x), G.bar(y))
                need(G.vec[c] == tuple(p * v for v in b), 'COMMUTATOR_' + name)
        levels, norm, allsg = subgroups(G)
        counts = [len(l) for l in levels]
        need(all(c % p == 1 for c in counts), 'SYLOW_COUNT_' + name)
        order_p = sum(1 for x in range(G.n) if x and G.pw[x] == 0)
        need(counts[1] * (p - 1) == order_p, 'ORDER_P_COUNT_' + name)
        r, ranks = rho(p, d, beta)
        ell, chain = cyclic_length(G, levels, norm)
        verify_chain(G, chain)
        need(ell >= d + r, 'BOUND_' + name)
        inv = proof_invariants(G, beta, levels, norm)
        ell_glob, _ = cyclic_length(G, levels, norm, global_normal=True)
        ell_nocyc, _ = cyclic_length(G, levels, norm, ignore_cyclic=True)
        res.append({'case': name, 'p': p, 'd': d, 'order': G.n, 'subgroups': len(allsg),
                    'subgroups_by_order': counts, 'form_ranks': ranks, 'rho': r, 'ell': ell,
                    'bound': d + r, 'p2_edges_checked': inv, 'ell_globally_normal_chains': ell_glob,
                    'ell_if_cyclicity_ignored': ell_nocyc})
    # negative controls on the finite checker
    neg = []
    gq = res[0]
    neg.append({'control': 'mutated-bound-d+rho+1', 'rejected': gq['ell'] < gq['bound'] + 1})
    bad = lambda x, y: tuple((x[0] * x[0] * y[1]) % 3 if k == 0 else 0 for k in range(3))
    neg.append({'control': 'non-bilinear-correction-cocycle', 'rejected': not cocycle_exhaustive(3, 3, bad)})
    sym = lambda x, y: tuple((x[0] * y[1] + x[1] * y[0]) % 3 if k == 2 else 0 for k in range(3))
    Gs = Group(3, 3, sym)
    neg.append({'control': 'symmetric-beta-commutator-identity', 'rejected': any(
        Gs.vec[Gs.T[Gs.T[Gs.T[x][y]][Gs.inv[x]]][Gs.inv[y]]] != tuple(3 * v for v in sym(Gs.bar(x), Gs.bar(y)))
        for x in range(Gs.n) for y in range(Gs.n))})
    G = Group(3, 3, beta_gq(3, 3))
    levels, norm, _ = subgroups(G)
    dropped = [set(l) for l in levels]
    victim = sorted(dropped[2])[0]
    dropped[2].discard(victim)
    neg.append({'control': 'dropped-subgroup-count', 'rejected': len(dropped[2]) % 3 != 1})
    neg.append({'control': 'ignore-cyclicity-breaks-bound', 'rejected': gq['ell_if_cyclicity_ignored'] < gq['bound']})
    for c in neg:
        need(c['rejected'], 'NEGATIVE_CONTROL_' + c['control'])
    return {'cases': res, 'negative_controls': neg,
            'limits': 'finite instances only; associativity sampled plus exhaustive cocycle; not a proof'}


def review_identity(review_dir, expected):
    """Verify this review directory against its externally reported REVIEW-MANIFEST.json hash."""
    need(isinstance(expected, str) and re.fullmatch('[0-9a-f]{64}', expected) is not None, 'EXPECTED_FORMAT')
    raw = (review_dir / 'REVIEW-MANIFEST.json').read_bytes()
    need(sha256(raw) == expected, 'REVIEW_MANIFEST_ANCHOR')
    m = json.loads(raw)
    entries = list(review_dir.rglob('*'))
    need(not any(e.is_symlink() for e in entries), 'SYMLINK')
    files = {str(e.relative_to(review_dir)) for e in entries if e.is_file()} - {'REVIEW-MANIFEST.json'}
    need(files == set(m['files']), 'MEMBERSHIP')
    for f, h in m['files'].items():
        need(sha256((review_dir / f).read_bytes()) == h, 'PAYLOAD_HASH')
    return {'review_identity': 'verified', 'payloads': len(files)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['identity', 'controls', 'finite', 'review-identity'])
    ap.add_argument('--expected', required=True)
    ap.add_argument('--packet', type=Path)
    ap.add_argument('--tree', type=Path)
    ap.add_argument('--scratch', type=Path)
    ap.add_argument('--review', type=Path, default=Path(__file__).resolve().parent)
    a = ap.parse_args()
    try:
        if a.mode == 'review-identity':
            out = review_identity(a.review, a.expected)
            print(json.dumps(out, sort_keys=True))
            return
        need(a.packet is not None and a.tree is not None, 'PACKET_AND_TREE_REQUIRED')
        if a.mode == 'identity':
            out = identity(a.packet, a.expected, a.tree)
        elif a.mode == 'controls':
            need(a.scratch is not None and str(a.scratch.resolve()).startswith('/var/tmp/'), 'SCRATCH_LOCATION')
            out = controls(a.packet, a.expected, a.tree, a.scratch)
        else:
            out = finite(a.packet, a.expected, a.tree)
        print(json.dumps(out, sort_keys=True))
    except (Reject, OSError, KeyError, ValueError) as e:
        print('REJECT: ' + str(e))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
