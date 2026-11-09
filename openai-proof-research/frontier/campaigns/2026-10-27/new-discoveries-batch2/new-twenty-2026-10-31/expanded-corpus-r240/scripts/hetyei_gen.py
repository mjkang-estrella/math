"""347231 (Hetyei Conjecture 5.15) and kernel dimensions (347230) per degree, exact over Q.
Uses MODULE (hetyei_literal_vbu.py = poset-correct operator, or hetyei_literal.py = printed M).
For n = 1..NMAX: rank of I2 on Q<a,b>_n, dim ker vs dim A_n; span of all n-fold compositions of
Pyr(u) = M(1,u) and L applied to 1, with L = Lhet: u -> (a-b)u + u(a-b)  (Hetyei Lemma 5.11)
or L = Ler: u -> (a-b)u (the Ehrenborg-Readdy lift quoted in the MathDB paraphrase); compare with dim S_n.
Also checks every composition is an I2-eigenvector and records eigenvalues.
Usage: hetyei_gen.py MODULE NMAX SCRIPTDIR"""
import sys, itertools, importlib.util
from fractions import Fraction
SD = sys.argv[-1]
spec = importlib.util.spec_from_file_location('hl', SD + '/' + sys.argv[1]); hl = importlib.util.module_from_spec(spec)
sys_argv_backup = sys.argv
spec.loader.exec_module(hl)
NMAX = int(sys.argv[2])
def add(d, w, c):
    if c:
        d[w] = d.get(w, 0) + c
        if d[w] == 0: del d[w]
def lin(f, vec):
    out = {}
    for w, c in vec.items():
        for w2, d in f(w).items(): add(out, w2, c * d)
    return out
def Pyr(vec): return lin(lambda w: hl.M('', w), vec)
def Lhet(vec):
    out = {}
    for w, c in vec.items():
        add(out, 'a' + w, c); add(out, 'b' + w, -c); add(out, w + 'a', c); add(out, w + 'b', -c)
    return out
def Ler(vec):
    out = {}
    for w, c in vec.items():
        add(out, 'a' + w, c); add(out, 'b' + w, -c)
    return out
def rank(vecs, n):
    W = hl.words(n); idx = {w: i for i, w in enumerate(W)}
    rows = []
    for v in vecs:
        r = [Fraction(0)] * len(W)
        for w, c in v.items(): r[idx[w]] = Fraction(c)
        rows.append(r)
    rk, _ = hl.rref_kernel(rows, len(W)) if rows else (0, [])
    return rk
for Lname, L in (('Lhet', Lhet), ('Ler', Ler)):
    level = [{'': 1}]
    for n in range(1, NMAX + 1):
        level = [Pyr(v) for v in level] + [L(v) for v in level]
        dimS = 2 ** (n - 1) + 2 ** ((n - 1) // 2)
        # eigen check
        eig = set(); noneig = 0; nonsym = 0
        for v in level:
            if not v: continue
            img = hl.I2word if False else None
            Iv = lin(hl.I2word, v)
            w0, c0 = next(iter(v.items()))
            lam = Fraction(Iv.get(w0, 0), c0)
            if any(Iv.get(w, 0) != lam * c for w, c in v.items()) or any(w not in v for w in Iv): noneig += 1
            else: eig.add(lam)
            if any(v.get(w[::-1], 0) != c for w, c in v.items()): nonsym += 1
        rk = rank([v for v in level if v], n)
        print(Lname, 'n', n, 'compositions', len(level), 'span dim', rk, 'dim S_n', dimS,
              'non-eigenvectors', noneig, 'non-symmetric', nonsym, 'eigenvalues', sorted(eig), flush=True)
# kernel dimensions
for n in range(1, NMAX + 1):
    W = hl.words(n)
    rows = []
    idx = {w: i for i, w in enumerate(W)}
    for u in W:
        r = [Fraction(0)] * len(W)
        for w, c in hl.I2word(u).items(): r[idx[w]] = Fraction(c)
        rows.append(r)
    rk, ker = hl.rref_kernel(rows, len(W))
    print('KERNEL n', n, 'rank', rk, 'dim ker', len(ker), 'dim A_n', 2 ** (n - 1) - 2 ** ((n - 1) // 2), flush=True)
