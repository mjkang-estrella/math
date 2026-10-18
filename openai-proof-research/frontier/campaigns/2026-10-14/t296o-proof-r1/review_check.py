"""Independent T296O proof-review checks: packet identity, integrity controls, finite diagnostics.

Provenance: the identity/controls/review-identity structure is adapted from the
campaign helper frontier/campaigns/2026-10-14/t314c-proof-r1/review_check.py
(lines 1-172 and 519-564 read: identity, controls, review-identity, main),
and the link/nonregular/hardlink/directory checks from the author verifier
fresh-structural-discovery-r77/verify.py (read in full). The finite
algebra below is reviewer code written from scratch; nothing is imported from
the author packet.

Identity checks certify byte identity and provenance only. Finite diagnostics
are exact computations in the group von Neumann algebra of K * F with K finite;
they test individual algebraic identities on small instances and certify no
theorem.

Usage:
    python3 -B review_check.py identity --expected AUTHOR_MANIFEST_SHA --packet DIR --tree TREE
    python3 -B review_check.py controls --expected AUTHOR_MANIFEST_SHA --packet DIR --tree TREE --scratch /var/tmp/...
    python3 -B review_check.py finite
    python3 -B review_check.py seal
    python3 -B review_check.py review-identity --expected REVIEW_MANIFEST_SHA
    python3 -B review_check.py review-controls --expected REVIEW_MANIFEST_SHA --scratch /var/tmp/...
"""
import argparse, hashlib, itertools, json, os, random, re, shutil, stat, subprocess, sys
from fractions import Fraction as Fr
from pathlib import Path

AUTHOR_ANCHORS = {
    'scope-freeze.md': '66056cf6b75951e864e69b51386d9729389f3b96f67e62b6cf5064eff9101a5b',
    'candidate.md': 'da41f84da4934967b185ce33551dabf8b4c02ab76b711f5103fe40cded4ac857',
    'comparison.md': 'fe6bfb5ca0962589cb9150ef82449ea0f5ddb144e9b05e5b6204b97399f058f6',
    'reading-limits.md': '86522bd021c1c20f9e3a61cfb970b3a469fec9ea2370721e70dc4d46ba70fc50',
}
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
TREE_ENTRIES = 13223
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
FAMILY = 'Relative-generation-and-the-generator-problem-for-finite-factors-'
SECTION_LABELS = {
    'independence.tex': ['\\label{lem:free-haar-extension}', '\\label{lem:haar-absorption}'],
    'perturbation.tex': ['\\label{lem:length-one-convolution}', '\\label{prop:perturbation}'],
    'generation.tex': ['\\label{lem:projection-continuity}', '\\label{lem:unitary-completeness}'],
    'introduction.tex': ['\\label{thm:relative-generation}', 'for the trace $2$-norm topology.'],
}
REVIEW_MANIFEST = 'REVIEW-MANIFEST.json'


class Reject(Exception):
    pass


def need(ok, reason):
    if not ok:
        raise Reject(reason)


def sha256(b):
    return hashlib.sha256(b).hexdigest()


def git_blob(b):
    return hashlib.sha1(b'blob %d\0' % len(b) + b).hexdigest()


def strict_tree(root):
    """Reject links, hard links and nonregular entries; return (files, dirs) relative names."""
    need(root.is_dir() and not root.is_symlink(), 'ROOT')
    files, dirs = set(), set()
    for x in [root, *root.rglob('*')]:
        st = x.lstat()
        need(not stat.S_ISLNK(st.st_mode), 'SYMLINK')
        need(stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode), 'NONREGULAR')
        rel = '.' if x == root else str(x.relative_to(root))
        if stat.S_ISREG(st.st_mode):
            need(st.st_nlink == 1, 'HARDLINK')
            files.add(rel)
        else:
            dirs.add(rel)
    return files, dirs


# ---------------------------------------------------------------- author packet identity

def identity(packet, expected, tree):
    need(isinstance(expected, str) and re.fullmatch('[0-9a-f]{64}', expected) is not None, 'EXPECTED_FORMAT')
    files, dirs = strict_tree(packet)
    raw = (packet / 'MANIFEST.json').read_bytes()
    need(sha256(raw) == expected, 'MANIFEST_ANCHOR')
    m = json.loads(raw)
    need(set(m) == files - {'MANIFEST.json'}, 'MEMBERSHIP')
    want_dirs = {'.'}
    for name, v in m.items():
        q = Path(name)
        need(not q.is_absolute() and '..' not in q.parts, 'UNSAFE_PATH')
        want_dirs.update(str(z) for z in q.parents)
        b = (packet / q).read_bytes()
        need(sha256(b) == v['sha256'] and len(b) == v['bytes'], 'PAYLOAD_HASH')
    need(want_dirs == dirs, 'DIRECTORIES')
    for name, h in AUTHOR_ANCHORS.items():
        need(sha256((packet / name).read_bytes()) == h, 'ANCHOR:' + name)
    cand = (packet / 'candidate.md').read_text()
    need('is a dense G_delta subset of U(M) in the operator norm' in cand and 'nonscalar u∈U(M)' in cand,
         'CANDIDATE_STATEMENT')
    tb = tree.read_bytes()
    need(sha256(tb) == TREE_SHA, 'TREE_ANCHOR')
    t = json.loads(tb)
    need(t.get('truncated') is False and len(t['tree']) == TREE_ENTRIES, 'TREE_SHAPE')
    canon = {e['path']: e for e in t['tree']}
    need(len(canon) == TREE_ENTRIES, 'TREE_UNIQUE')
    s = json.loads((packet / 'source-receipts.json').read_bytes())
    need(s['pin'] == PIN and s['tree_sha256'] == TREE_SHA, 'SOURCE_PIN')
    wanted = {e['path'] for e in t['tree'] if e['type'] == 'blob' and FAMILY in e['path']
              and not e['path'].endswith('.pdf')}
    need(len(wanted) == 9 and {v['source_path'] for v in s['files']} == wanted and len(s['files']) == 9,
         'SOURCE_MEMBERSHIP')
    seen_labels = set()
    for v in s['files']:
        need(v['url'] == f'https://raw.githubusercontent.com/openai/math/{PIN}/{v["source_path"]}', 'SOURCE_URL')
        b = (packet / v['path']).read_bytes()
        g = git_blob(b)
        need(g == v['git_blob'] == canon[v['source_path']]['sha'], 'SOURCE_BLOB')
        need(sha256(b) == v['sha256'] and len(b) == v['bytes'], 'SOURCE_SHA')
        base = Path(v['source_path']).name
        if base in SECTION_LABELS:
            txt = b.decode()
            need(all(lbl in txt for lbl in SECTION_LABELS[base]), 'SOURCE_LABEL:' + base)
            seen_labels.add(base)
    need(seen_labels == set(SECTION_LABELS), 'SOURCE_LABEL_COVERAGE')
    for v in json.loads((packet / 'primary-receipts.json').read_bytes()):
        need(sha256((packet / v['file']).read_bytes()) == v['sha256'], 'PRIMARY_RECEIPT')
        need(sha256((packet / v['text_file']).read_bytes()) == v['text_sha256'], 'PRIMARY_RECEIPT')
    return {'identity': 'verified', 'payloads': len(m), 'directories': len(dirs), 'source_blobs': 9,
            'tree_entries': TREE_ENTRIES, 'limits': 'byte identity/provenance only; no theorem'}


def run_sub(args):
    r = subprocess.run([sys.executable, '-B', __file__, *args], capture_output=True, text=True)
    return r.returncode, r.stdout.strip()


def reseal_author(packet):
    mp = packet / 'MANIFEST.json'
    m = json.loads(mp.read_bytes())
    for f in m:
        b = (packet / f).read_bytes()
        m[f] = {'sha256': sha256(b), 'bytes': len(b)}
    b = json.dumps(m, indent=2).encode()
    mp.write_bytes(b)
    return sha256(b)


def flip(path):
    b = bytearray(path.read_bytes())
    b[len(b) // 2] ^= 1
    path.write_bytes(bytes(b))


def scratch_ok(p):
    need(p is not None and str(p.resolve()).startswith('/var/tmp/'), 'SCRATCH_LOCATION')


def controls(packet, expected, tree, scratch):
    identity(packet, expected, tree)
    scratch_ok(scratch)
    scratch.mkdir(parents=True, exist_ok=True)
    out = []
    base = scratch / 'author-copy'
    if base.exists():
        shutil.rmtree(base)
    shutil.copytree(packet, base, symlinks=True)
    rc, s = run_sub(['identity', '--expected', expected, '--packet', str(base), '--tree', str(tree)])
    need(rc == 0 and json.loads(s)['identity'] == 'verified', 'POSITIVE_COPY')
    out.append({'control': 'positive-copied-packet', 'result': 'accepted'})
    shutil.rmtree(base)

    def trial(name, reason, mutate):
        p = scratch / name
        if p.exists():
            shutil.rmtree(p)
        shutil.copytree(packet, p, symlinks=True)
        tr = scratch / (name + '-tree.json')
        shutil.copyfile(tree, tr)
        exp = mutate(p, tr) or expected
        rc, s = run_sub(['identity', '--expected', exp, '--packet', str(p), '--tree', str(tr)])
        need(rc != 0 and s == 'REJECT: ' + reason, 'CONTROL_' + name + ':' + s)
        out.append({'control': name, 'rejection': reason})
        shutil.rmtree(p)
        tr.unlink()

    trial('wrong-anchor', 'MANIFEST_ANCHOR', lambda p, t: '0' * 64)
    trial('malformed-anchor', 'EXPECTED_FORMAT', lambda p, t: 'abc')
    trial('candidate-flip', 'PAYLOAD_HASH', lambda p, t: flip(p / 'candidate.md'))
    trial('candidate-flip-resealed', 'ANCHOR:candidate.md', lambda p, t: (flip(p / 'candidate.md'), reseal_author(p))[1])
    trial('scope-flip-resealed', 'ANCHOR:scope-freeze.md', lambda p, t: (flip(p / 'scope-freeze.md'), reseal_author(p))[1])
    trial('extra-file', 'MEMBERSHIP', lambda p, t: (p / 'extra.md').write_text('x') and None)
    trial('missing-file', 'MEMBERSHIP', lambda p, t: (p / 'checkpoint.md').unlink())
    trial('extra-empty-dir', 'DIRECTORIES', lambda p, t: (p / 'private' / 'empty').mkdir())
    trial('symlink', 'SYMLINK', lambda p, t: os.symlink('candidate.md', p / 'link.md'))
    trial('hardlink', 'HARDLINK', lambda p, t: os.link(p / 'candidate.md', p / 'private' / 'hl.md'))
    trial('fifo', 'NONREGULAR', lambda p, t: os.mkfifo(p / 'pipe'))
    trial('tree-flip', 'TREE_ANCHOR', lambda p, t: flip(t))

    def source_mut(p, t):
        rp = p / 'source-receipts.json'
        r = json.loads(rp.read_bytes())
        for e in r['files']:
            if e['source_path'].endswith('perturbation.tex'):
                f = p / e['path']
                f.write_bytes(f.read_bytes().replace(b'\\le\\frac{4\\alpha^2}{1-2\\alpha}', b'\\le\\frac{\\alpha^2}{1-2\\alpha}'))
                e['sha256'] = sha256(f.read_bytes())
                e['bytes'] = len(f.read_bytes())
        rp.write_bytes(json.dumps(r, indent=2).encode())
        return reseal_author(p)
    trial('source-estimate-edit-resealed', 'SOURCE_BLOB', source_mut)

    def url_mut(p, t):
        rp = p / 'source-receipts.json'
        r = json.loads(rp.read_bytes())
        r['files'][0]['url'] = r['files'][0]['url'].replace(PIN, 'main')
        rp.write_bytes(json.dumps(r, indent=2).encode())
        return reseal_author(p)
    trial('unpinned-url-resealed', 'SOURCE_URL', url_mut)

    def primary_mut(p, t):
        flip(p / 'private' / 'primary' / 'similarity.txt')
        return reseal_author(p)
    trial('primary-text-flip-resealed', 'PRIMARY_RECEIPT', primary_mut)
    return out


# ---------------------------------------------------------------- review directory identity

def seal(review_dir):
    files, dirs = strict_tree(review_dir)
    files.discard(REVIEW_MANIFEST)
    m = {'files': {f: {'sha256': sha256((review_dir / f).read_bytes()),
                       'bytes': (review_dir / f).stat().st_size} for f in sorted(files)},
         'directories': sorted(dirs)}
    b = json.dumps(m, indent=2, sort_keys=True).encode() + b'\n'
    (review_dir / REVIEW_MANIFEST).write_bytes(b)
    return {'sealed': sha256(b), 'payloads': len(files)}


def review_identity(review_dir, expected):
    need(isinstance(expected, str) and re.fullmatch('[0-9a-f]{64}', expected) is not None, 'EXPECTED_FORMAT')
    files, dirs = strict_tree(review_dir)
    raw = (review_dir / REVIEW_MANIFEST).read_bytes()
    need(sha256(raw) == expected, 'REVIEW_MANIFEST_ANCHOR')
    m = json.loads(raw)
    need(files - {REVIEW_MANIFEST} == set(m['files']), 'MEMBERSHIP')
    need(dirs == set(m['directories']), 'DIRECTORIES')
    for f, v in m['files'].items():
        need(not Path(f).is_absolute() and '..' not in Path(f).parts, 'UNSAFE_PATH')
        b = (review_dir / f).read_bytes()
        need(sha256(b) == v['sha256'] and len(b) == v['bytes'], 'PAYLOAD_HASH')
    return {'review_identity': 'verified', 'payloads': len(m['files'])}


def review_controls(review_dir, expected, scratch):
    review_identity(review_dir, expected)
    scratch_ok(scratch)
    scratch.mkdir(parents=True, exist_ok=True)
    out = []

    def trial(name, reason, mutate):
        p = scratch / name
        if p.exists():
            shutil.rmtree(p)
        shutil.copytree(review_dir, p, symlinks=True)
        exp = (mutate(p) if mutate else None) or expected
        rc, s = run_sub(['review-identity', '--expected', exp, '--review', str(p)])
        if reason is None:
            need(rc == 0 and json.loads(s)['review_identity'] == 'verified', 'POSITIVE_COPY')
            out.append({'control': name, 'result': 'accepted'})
        else:
            need(rc != 0 and s == 'REJECT: ' + reason, 'CONTROL_' + name + ':' + s)
            out.append({'control': name, 'rejection': reason})
        shutil.rmtree(p)

    trial('positive-copied-review', None, None)
    trial('wrong-anchor', 'REVIEW_MANIFEST_ANCHOR', lambda p: 'f' * 64)
    trial('review-flip', 'PAYLOAD_HASH', lambda p: flip(p / 'review.md'))
    trial('extra-file', 'MEMBERSHIP', lambda p: (p / 'extra.md').write_text('x') and None)
    trial('missing-file', 'MEMBERSHIP', lambda p: (p / 'reading-limits.md').unlink())
    trial('extra-empty-dir', 'DIRECTORIES', lambda p: (p / 'empty').mkdir())
    trial('symlink', 'SYMLINK', lambda p: os.symlink('review.md', p / 'link.md'))
    trial('hardlink', 'HARDLINK', lambda p: os.link(p / 'review.md', p / 'hl.md'))
    trial('fifo', 'NONREGULAR', lambda p: os.mkfifo(p / 'pipe'))

    def verdict_resealed(p):
        f = p / 'review.md'
        f.write_bytes(f.read_bytes().replace(b'PASS_FULL_T296O', b'FAIL_FULL_T296O', 1))
        return None
    trial('verdict-edit-not-resealed', 'PAYLOAD_HASH', verdict_resealed)
    return out


# ---------------------------------------------------------------- exact Gaussian rationals

Z = (Fr(0), Fr(0))
ONE = (Fr(1), Fr(0))
I = (Fr(0), Fr(1))


def g(re_, im=0):
    return (Fr(re_), Fr(im))


def cadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def cconj(a):
    return (a[0], -a[1])


def cabs2(a):
    return a[0] * a[0] + a[1] * a[1]


def cneg(a):
    return (-a[0], -a[1])


# ---------------------------------------------------------------- group algebra of K * F

class FiniteGroup:
    def __init__(self, n, mul, name):
        self.n, self.mt, self.name = n, mul, name
        self.inv = [next(b for b in range(n) if mul[a][b] == 0) for a in range(n)]


def z2m(m):
    n = 1 << m
    return FiniteGroup(n, [[a ^ b for b in range(n)] for a in range(n)], f'Z2^{m}')


def s3():
    perms = list(itertools.permutations(range(3)))
    perms.sort(key=lambda p: p != (0, 1, 2))
    idx = {p: i for i, p in enumerate(perms)}
    mul = [[idx[tuple(a[b[x]] for x in range(3))] for b in perms] for a in perms]
    G = FiniteGroup(6, mul, 'S3')
    G.perms = perms
    return G


class Alg:
    """Group algebra of K * F; words alternate K letters ('k', i>0) and nonzero ints (F letters)."""

    def __init__(self, K):
        self.K = K

    def push(self, s, x):
        K = self.K
        if isinstance(x, int):
            if s and isinstance(s[-1], int) and s[-1] == -x:
                s.pop()
            else:
                s.append(x)
        else:
            if s and not isinstance(s[-1], int):
                y = K.mt[s.pop()[1]][x[1]]
                if y:
                    s.append(('k', y))
            elif x[1]:
                s.append(x)

    def wmul(self, a, b):
        s = list(a)
        for x in b:
            self.push(s, x)
        return tuple(s)

    def winv(self, w):
        return tuple(-x if isinstance(x, int) else ('k', self.K.inv[x[1]]) for x in reversed(w))

    def mul(self, X, Y):
        out = {}
        for a, ca in X.items():
            for b, cb in Y.items():
                w = self.wmul(a, b)
                out[w] = cadd(out.get(w, Z), cmul(ca, cb))
        return {w: c for w, c in out.items() if c != Z}

    def prod(self, *Xs):
        out = {(): ONE}
        for X in Xs:
            out = self.mul(out, X)
        return out

    def add(self, X, Y, sign=ONE):
        out = dict(X)
        for w, c in Y.items():
            out[w] = cadd(out.get(w, Z), cmul(sign, c))
        return {w: c for w, c in out.items() if c != Z}

    def adj(self, X):
        return {self.winv(w): cconj(c) for w, c in X.items()}

    def tr(self, X):
        return X.get((), Z)

    def pair(self, X, Y):
        """tau(XY) without forming XY."""
        tot = Z
        for w, c in X.items():
            d = Y.get(self.winv(w))
            if d is not None:
                tot = cadd(tot, cmul(c, d))
        return tot

    def norm2sq(self, X):
        return sum((cabs2(c) for c in X.values()), Fr(0))

    def gen(self, i):
        return {(i,): ONE}

    def kel(self, i, c=ONE):
        return {(('k', i),) if i else (): c}

    def from_k(self, coeffs):
        return {(('k', i),) if i else (): c for i, c in enumerate(coeffs) if c != Z}


def spectral_unitary(m, lams):
    """u = sum_chi lam_chi e_chi in L(Z2^m); e_chi = 2^-m sum_g (-1)^{<chi,g>} g."""
    n = 1 << m
    co = [Z] * n
    for chi, lam in enumerate(lams):
        for gg in range(n):
            sgn = -1 if bin(chi & gg).count('1') % 2 else 1
            co[gg] = cadd(co[gg], cmul(g(Fr(sgn, n)), lam))
    return co


def s3_unitary(G, k, lams):
    """u = k * (l1 z_triv + l2 z_sign + l3 z_std) with central projections of L(S3)."""
    sgn = [1 if sum(1 for i in range(3) for j in range(i + 1, 3) if p[i] > p[j]) % 2 == 0 else -1
           for p in G.perms]
    ztr = [g(Fr(1, 6))] * 6
    zsg = [g(Fr(s, 6)) for s in sgn]
    zst = [cneg(cadd(ztr[i], zsg[i])) for i in range(6)]
    zst[0] = cadd(zst[0], ONE)
    c = [cadd(cadd(cmul(lams[0], ztr[i]), cmul(lams[1], zsg[i])), cmul(lams[2], zst[i])) for i in range(6)]
    out = [Z] * 6
    for i in range(6):
        out[G.mt[k][i]] = cadd(out[G.mt[k][i]], c[i])
    return out


def is_unitary(A, X):
    return A.mul(A.adj(X), X) == {(): ONE} and A.mul(X, A.adj(X)) == {(): ONE}


U5 = g(Fr(3, 5), Fr(4, 5))
U13 = g(Fr(5, 13), Fr(12, 13))
U17 = g(Fr(8, 17), Fr(-15, 17))


def laws():
    out = []
    for name, m, lu, lz, xi, ells in [
        ('Z2: eigen (1,i)', 1, [ONE, I], [g(-1), U5], [g(2, 1), g(-1, 3)], [1, 2, 3, 4]),
        ('Z2: eigen (1,(3+4i)/5)', 1, [ONE, U5], [U13, I], [g(1), g(0, -2)], [1, 2, 3]),
        ('Z2^2: atom 3/4 (1,1,1,i)', 2, [ONE, ONE, ONE, I], [g(-1), U5, I, ONE], [g(1, 1), g(2), g(0, 1), g(-1)], [1, 2, 3]),
        ('Z2^2: (1,-1,i,(5+12i)/13)', 2, [ONE, g(-1), I, U13], [U17, g(-1), U5, I], [g(3), g(1, -1), g(0), g(2, 2)], [1, 2]),
        ('Z2^2: scalar endpoint i', 2, [I, I, I, I], [g(-1), U5, I, ONE], [g(1, 1), g(2), g(0, 1), g(-1)], [1, 2]),
        ('Z2^3: eight atoms', 3, [ONE, I, g(-1), g(0, -1), U5, cconj(U5), U13, ONE],
         [U17, ONE, I, g(-1), ONE, U5, ONE, I], [g(1), g(0, 1), g(2), g(-1), g(1, 1), g(0), g(3), g(-2)], [1]),
    ]:
        K = z2m(m)
        out.append((name, K, spectral_unitary(m, lu), spectral_unitary(m, lz), xi, ells))
    G = s3()
    out.append(('S3 nonabelian: transposition * central phases', G, s3_unitary(G, 1, [I, ONE, U5]),
                s3_unitary(G, 3, [g(-1), U13, I]), [g(1), g(0, 2), g(-1), g(1, 1), g(0), g(2, -1)], [1, 2]))
    return out


# ---------------------------------------------------------------- finite diagnostics

def first_order(rec, neg):
    """Exact conjugation response (3), (4), (5) with honest y = z W*, t_j free generators of F."""
    checks = 0
    for name, K, ucoef, zcoef, xicoef, ells in laws():
        A = Alg(K)
        u, z, xi = A.from_k(ucoef), A.from_k(zcoef), A.from_k(xicoef)
        need(is_unitary(A, u) and is_unitary(A, z), 'MODEL_UNITARY')
        tu = A.tr(u)
        beta = cadd(ONE, cneg(cmul(tu, cconj(tu))))
        xs = A.adj(xi)
        txz = A.pair(xs, z)
        for ell in ells:
            t = [A.gen(j + 1) for j in range(ell + 1)]
            s = [None, t[0]] + [A.mul(u, t[j]) for j in range(1, ell + 1)]
            gk = [None]
            cur = {(): ONE}
            for k in range(1, ell + 1):
                cur = A.mul(cur, s[k])
                gk.append(cur)
            W = A.mul(A.mul(gk[ell], u), t[ell])
            y = A.mul(z, A.adj(W))
            ys = A.adj(y)
            need(A.pair(xs, W) == Z, 'TAU_XI_W')
            checks += 1
            resp = Z
            resp_p_only = Z
            for k in range(1, ell + 1):
                for j in range(1, ell + 1):
                    for kind, lab in (('p', A.mul(gk[k], A.adj(gk[j]))),
                                      ('q', A.prod(gk[k], u, A.adj(gk[j])))):
                        labs = A.adj(lab)
                        right = A.mul(labs, W)
                        fwd = A.pair(A.prod(xs, lab, y), right)
                        bwd = A.pair(A.prod(xs, lab, ys), right)
                        # (3) and (4) for this label in U(D_ell)
                        need(fwd == cmul(A.pair(A.mul(xs, lab), z), A.tr(labs)), 'EQ3')
                        need(bwd == Z, 'EQ4')
                        checks += 2
                        term = cadd(fwd, cneg(bwd))
                        if kind == 'p':
                            resp = cadd(resp, term)
                            resp_p_only = cadd(resp_p_only, term)
                        else:
                            resp = cadd(resp, cneg(term))
            # (5) with c factored out: tau(xi^* S W) = ell * beta * tau(xi^* z)
            need(resp == cmul(cmul(g(ell), beta), txz), 'EQ5')
            checks += 1
            if txz != Z and tu != Z and tu[1] != 0:
                wrong = cadd(ONE, cneg(cmul(tu, tu)))
                neg['beta_with_trace_squared_not_abs_squared'] = neg.get(
                    'beta_with_trace_squared_not_abs_squared', 0) + int(resp != cmul(cmul(g(ell), wrong), txz))
            if txz != Z and tu != Z:
                neg['omit_conjugation_right_factor'] = neg.get('omit_conjugation_right_factor', 0) + int(
                    resp_p_only != cmul(cmul(g(ell), beta), txz))
        rec.append({'law': name, 'K': K.name, 'trace_u': [str(x) for x in tu], 'beta': str(beta[0]),
                    'ells': ells})
    return checks


def lemma21_random(neg):
    """Words in unitary D letters and free letters: nonidentity degree => trace 0."""
    checks = 0
    nonvacuous = 0
    rng = random.Random(29601)
    for name, K, ucoef, zcoef, xicoef, ells in laws():
        A = Alg(K)
        u, z = A.from_k(ucoef), A.from_k(zcoef)
        dl = [u, A.adj(u), z, A.adj(z), A.mul(u, z)]
        for _ in range(60):
            word, deg = [], ()
            for _ in range(rng.randrange(3, 9)):
                if rng.randrange(2):
                    word.append(rng.choice(dl))
                else:
                    x = rng.choice([1, 2, 3, -1, -2, -3])
                    word.append(A.gen(x))
                    deg = A.wmul(deg, (x,))
            val = A.tr(A.prod(*word))
            if deg:
                need(val == Z, 'LEMMA21')
                checks += 1
            elif val != Z:
                nonvacuous += 1
    neg['identity_degree_words_with_nonzero_trace'] = nonvacuous
    return checks


def factorization_matrices(neg):
    """Exact identity (2) for arbitrary unitary w, with 3x3 Cayley unitaries over Q(i)."""
    n = 3
    rng = random.Random(29602)

    def mm(X, Y):
        return [[sum_c(cmul(X[i][k], Y[k][j]) for k in range(n)) for j in range(n)] for i in range(n)]

    def sum_c(it):
        tot = Z
        for x in it:
            tot = cadd(tot, x)
        return tot

    def ad(X):
        return [[cconj(X[j][i]) for j in range(n)] for i in range(n)]

    def eye():
        return [[ONE if i == j else Z for j in range(n)] for i in range(n)]

    def inv(X):
        M = [row[:] + eye()[i] for i, row in enumerate(X)]
        for c in range(n):
            p = next(r for r in range(c, n) if M[r][c] != Z)
            M[c], M[p] = M[p], M[c]
            d = M[c][c]
            dinv = (d[0] / cabs2(d), -d[1] / cabs2(d))
            M[c] = [cmul(dinv, x) for x in M[c]]
            for r in range(n):
                if r != c and M[r][c] != Z:
                    f = M[r][c]
                    M[r] = [cadd(M[r][k], cneg(cmul(f, M[c][k]))) for k in range(2 * n)]
        return [row[n:] for row in M]

    def cayley():
        B = [[g(rng.randint(-3, 3), rng.randint(-3, 3)) for _ in range(n)] for _ in range(n)]
        Aa = [[cadd(B[i][j], cneg(cconj(B[j][i]))) for j in range(n)] for i in range(n)]
        E = eye()
        U = mm([[cadd(E[i][j], cneg(Aa[i][j])) for j in range(n)] for i in range(n)],
               inv([[cadd(E[i][j], Aa[i][j]) for j in range(n)] for i in range(n)]))
        need(mm(ad(U), U) == E, 'CAYLEY_UNITARY')
        return U

    checks = 0
    reversed_fail = 0
    for ell in range(1, 5):
        for _ in range(2):
            u, w = cayley(), cayley()
            t = [cayley() for _ in range(ell + 1)]
            up = mm(mm(w, u), ad(w))
            Wp = t[0]
            W = t[0]
            for k in range(1, ell + 1):
                Wp = mm(mm(Wp, up), t[k])
                W = mm(mm(W, u), t[k])
            X = mm(up, ad(u))
            gk, cur = [], t[0]
            for k in range(1, ell + 1):
                gk.append(cur)
                cur = mm(mm(cur, u), t[k])
            rhs = eye()
            for G_ in gk:
                rhs = mm(rhs, mm(mm(G_, X), ad(G_)))
            need(mm(rhs, W) == Wp, 'EQ2')
            checks += 1
            if ell >= 2:
                rev = eye()
                for G_ in reversed(gk):
                    rev = mm(rev, mm(mm(G_, X), ad(G_)))
                reversed_fail += int(mm(rev, W) != Wp)
    neg['reversed_product_order_fails'] = reversed_fail
    return checks


def free_reduce(w):
    s = []
    for x in w:
        if s and s[-1] == -x:
            s.pop()
        else:
            s.append(x)
    return tuple(s)


def multiplicities(neg):
    checks = 0
    for ell in range(1, 31):
        cnt = {}
        for k in range(1, ell + 1):
            for j in range(1, ell + 1):
                p = free_reduce((k, -j))
                cnt[p] = cnt.get(p, 0) + 1
        need(cnt[()] == ell and all(v == 1 for p, v in cnt.items() if p), 'MULTIPLICITY')
        need(sum(v * v for v in cnt.values()) == 2 * ell * ell - ell, 'SUM_NP2')
        checks += 2
    neg['identity_label_counted_once'] = int(1 + 30 * 29 != 2 * 30 * 30 - 30)
    # Free family Y_p = p y p^{-1}, p in S (ell = 4, y = letter 99): random reduced Y-words are nonidentity.
    rng = random.Random(29603)
    S = sorted({free_reduce((k, -j)) for k in range(1, 5) for j in range(1, 5)})
    for _ in range(300):
        word, last = (), None
        for _ in range(rng.randrange(1, 7)):
            p = rng.choice([q for q in S if q != last])
            a = rng.choice([-2, -1, 1, 2])
            yl = (99,) * a if a > 0 else (-99,) * (-a)
            word = free_reduce(word + p + yl + tuple(-x for x in reversed(p)))
            last = p
        need(word != (), 'Y_FREE')
        checks += 1
    return checks


def remainder_envelope(rec, neg):
    """Coefficientwise doubled-row envelope env(C_d) <= (2A)^d and Lemma 2.1, c = 1, exact."""
    checks = 0
    cases = [(z2m(1), 1, 2), (z2m(1), 1, 3), (z2m(1), 2, 2), (z2m(1), 2, 3), (z2m(2), 2, 2), (z2m(1), 3, 2),
             (s3(), 2, 2)]
    lawmap = {'Z2^1': spectral_unitary(1, [ONE, I]), 'Z2^2': spectral_unitary(2, [ONE, ONE, I, U5])}
    for K, ell, d in cases:
        A = Alg(K)
        ucoef = lawmap.get(K.name) or s3_unitary(K, 1, [I, ONE, U5])
        u = A.from_k(ucoef)
        Y = ell + 1  # F0 free on G_1..G_ell (letters 1..ell) and y (letter ell+1)

        def Gw(k):
            return (k,)

        def Gi(k):
            return (-k,)
        # rows: formal words over symbols int / 'u' / 'U'
        rows = []
        for k in range(1, ell + 1):
            H, J = [], []
            for j in range(1, ell + 1):
                p = Gw(k) + Gi(j)
                H.append((g(1), p + (Y,) + tuple(-x for x in reversed(p))))
                H.append((g(-1), p + (-Y,) + tuple(-x for x in reversed(p))))
                q, qs = Gw(k) + ('u',) + Gi(j), Gw(j) + ('U',) + Gi(k)
                J.append((g(-1), q + (Y,) + qs))
                J.append((g(1), q + (-Y,) + qs))
            rows += [H, J]
        R = len(rows)
        formal = {}
        for seq in itertools.combinations_with_replacement(range(R), d):
            w8 = Fr(1)
            for r in set(seq):
                for f in range(2, seq.count(r) + 1):
                    w8 /= f
            for choice in itertools.product(*[rows[r] for r in seq]):
                c = g(w8)
                word = ()
                for cc, ww in choice:
                    c = cmul(c, cc)
                    word = word + ww
                formal[word] = cadd(formal.get(word, Z), c)
        env = {}
        actual = {}
        uel, Uel = u, A.adj(u)
        for word, c in formal.items():
            if c == Z:
                continue
            deg = free_reduce(tuple(x for x in word if isinstance(x, int)))
            need(c[1] == 0, 'REAL_ROW_COEFFICIENTS')
            env[deg] = env.get(deg, Fr(0)) + abs(c[0])
            X = {(): c}
            for x in word:
                X = A.mul(X, uel if x == 'u' else Uel if x == 'U' else A.gen(x))
            actual = A.add(actual, X)
        Aenv = {}
        for k in range(1, ell + 1):
            for j in range(1, ell + 1):
                p = free_reduce(Gw(k) + Gi(j))
                for e in (Y, -Y):
                    w = free_reduce(p + (e,) + tuple(-x for x in reversed(p)))
                    Aenv[w] = Aenv.get(w, 0) + 1

        def gmul(X, Yd):
            out = {}
            for a, ca in X.items():
                for b, cb in Yd.items():
                    w = free_reduce(a + b)
                    out[w] = out.get(w, 0) + ca * cb
            return out
        twoA = {w: 2 * v for w, v in Aenv.items()}
        P2, P1 = {(): 1}, {(): 1}
        for _ in range(d):
            P2 = gmul(P2, twoA)
            P1 = gmul(P1, Aenv)
        need(all(v <= P2.get(w, 0) for w, v in env.items()), 'ENVELOPE_DOUBLED')
        n2 = A.norm2sq(actual)
        e2 = sum((v * v for v in env.values()), Fr(0))
        p2 = sum(v * v for v in P2.values())
        haag = (16 * 2 * (2 * ell * ell - ell)) ** d
        need(n2 <= e2 <= p2 <= haag, 'NORM_CHAIN')
        checks += 2
        viol = sum(1 for w, v in env.items() if v > P1.get(w, 0))
        neg['single_row_envelope_violations'] = neg.get('single_row_envelope_violations', 0) + viol
        if d == 2:
            # all 2*ell rows meet the identity label once: C(2l,2) cross pairs + 2l halves = 2 l^2 > l^2 = A^2(y^2)
            need(env.get((Y, Y)) == 2 * ell * ell and P1.get((Y, Y)) == ell * ell, 'IDENTITY_LABEL_COLLISION')
            checks += 1
        rec.append({'K': K.name, 'ell': ell, 'd': d, 'formal_words': len(formal),
                    'actual_L2_sq': str(n2), 'envelope_l2_sq': str(e2), 'doubled_power_l2_sq': str(p2),
                    'haagerup_power_sq_bound_c1': str(haag), 'single_row_violations': viol})
    return checks


def finite():
    neg = {}
    fo, rem = [], []
    counts = {
        'first_order_and_eq3_eq4': first_order(fo, neg),
        'lemma21_random_words': lemma21_random(neg),
        'factorization_eq2_matrices': factorization_matrices(neg),
        'multiplicities_and_Y_freeness': multiplicities(neg),
        'remainder_envelope': remainder_envelope(rem, neg),
    }
    need(neg['beta_with_trace_squared_not_abs_squared'] > 0, 'NEG_BETA')
    need(neg['omit_conjugation_right_factor'] > 0, 'NEG_OMIT')
    need(neg['reversed_product_order_fails'] > 0, 'NEG_ORDER')
    need(neg['identity_label_counted_once'] == 1, 'NEG_MULT')
    need(neg['single_row_envelope_violations'] > 0, 'NEG_SINGLE_ROW')
    need(neg['identity_degree_words_with_nonzero_trace'] > 0, 'NEG_VACUOUS')
    return {'status': 'PASS', 'exact_checks': counts, 'total': sum(counts.values()),
            'negative_controls_detected': neg, 'first_order_laws': fo, 'remainder_cases': rem,
            'limits': 'Exact identities in L(K*F) for finite K and small ell, d; no infinite factor, '
                      'no ultrapower, no clipping, no Baire argument, no theorem.'}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['identity', 'controls', 'finite', 'seal', 'review-identity', 'review-controls'])
    ap.add_argument('--expected')
    ap.add_argument('--packet', type=Path)
    ap.add_argument('--tree', type=Path)
    ap.add_argument('--scratch', type=Path)
    ap.add_argument('--review', type=Path, default=Path(__file__).resolve().parent)
    a = ap.parse_args()
    try:
        if a.mode == 'finite':
            out = finite()
        elif a.mode == 'seal':
            out = seal(a.review)
        elif a.mode == 'review-identity':
            out = review_identity(a.review, a.expected)
        elif a.mode == 'review-controls':
            out = review_controls(a.review, a.expected, a.scratch)
        else:
            need(a.packet is not None and a.tree is not None, 'PACKET_AND_TREE_REQUIRED')
            if a.mode == 'identity':
                out = identity(a.packet, a.expected, a.tree)
            else:
                out = controls(a.packet, a.expected, a.tree, a.scratch)
        print(json.dumps(out, sort_keys=True))
    except (Reject, OSError, KeyError, ValueError, TypeError, StopIteration) as e:
        print('REJECT: ' + str(e))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
