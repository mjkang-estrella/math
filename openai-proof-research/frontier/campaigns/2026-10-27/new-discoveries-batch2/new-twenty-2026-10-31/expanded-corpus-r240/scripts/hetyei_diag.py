"""Diagnostics for Hetyei Lemma 5.11 / Corollary 5.13 with the poset-correct operator.
 (1) identity I2(M(u,v)) = M(I2 u, I2 v) on all word pairs with |u|+|v|+1 <= NMAX
 (2) which degree-3 compositions of Pyr, Lhet applied to 1 are not eigenvectors (with the path)
 (3) Lemma 5.11 test: for each eigenvector u among compositions of degree <= NMAX-1, is Lhet(u) an eigenvector?
 (4) does I2 commute with Lhet:  I2(L u) == L(I2 u) on all words of degree <= NMAX-1?
Usage: hetyei_diag.py NMAX SCRIPTDIR"""
import sys, importlib.util
from fractions import Fraction
SD = sys.argv[-1]
spec = importlib.util.spec_from_file_location('hl', SD + '/hetyei_literal_vbu.py'); hl = importlib.util.module_from_spec(spec); spec.loader.exec_module(hl)
NMAX = int(sys.argv[1])
def add(d, w, c):
    if c:
        d[w] = d.get(w, 0) + c
        if d[w] == 0: del d[w]
def lin(f, vec):
    out = {}
    for w, c in vec.items():
        for w2, d in f(w).items(): add(out, w2, c * d)
    return out
def I2(v): return lin(hl.I2word, v)
def Mv(x, y):
    out = {}
    for w1, c1 in x.items():
        for w2, c2 in y.items():
            for w, c in hl.M(w1, w2).items(): add(out, w, c1 * c2 * c)
    return out
def Lhet(vec):
    out = {}
    for w, c in vec.items():
        add(out, 'a' + w, c); add(out, 'b' + w, -c); add(out, w + 'a', c); add(out, w + 'b', -c)
    return out
def eigen(v):
    Iv = I2(v); w0, c0 = next(iter(v.items())); lam = Fraction(Iv.get(w0, 0), c0)
    ok = all(Iv.get(w, 0) == lam * c for w, c in v.items()) and all(w in v for w in Iv)
    return ok, lam
bad = 0; tot = 0
for n1 in range(0, NMAX):
    for n2 in range(0, NMAX - n1):
        for u in hl.words(n1):
            for v in hl.words(n2):
                tot += 1
                if I2(Mv({u: 1}, {v: 1})) != Mv(I2({u: 1}), I2({v: 1})): bad += 1
print('(1) I2(M(u,v)) == M(I2u, I2v): pairs', tot, 'failures', bad)
comps = [('', {'': 1})]
for n in range(1, NMAX):
    comps = [('P' + p, Mv({'': 1}, v)) for p, v in comps] + [('L' + p, Lhet(v)) for p, v in comps]
    for p, v in comps:
        if v and not eigen(v)[0] and n <= 3: print('(2) non-eigen composition (outermost first)', p, v)
# (3)
fail3 = 0; tot3 = 0
comps = [('', {'': 1})]
for n in range(1, NMAX):
    for p, v in comps:
        if v and eigen(v)[0]:
            tot3 += 1
            Lv = Lhet(v)
            if Lv and not eigen(Lv)[0]:
                fail3 += 1
                if fail3 <= 3: print('(3) eigenvector u =', p, v, 'eigenvalue', eigen(v)[1], 'but L(u) is not an eigenvector')
    comps = [('P' + p, Mv({'': 1}, v)) for p, v in comps] + [('L' + p, Lhet(v)) for p, v in comps]
print('(3) eigen compositions tested', tot3, 'L(u) non-eigen', fail3)
fail4 = 0; tot4 = 0
for n in range(0, NMAX):
    for u in hl.words(n):
        tot4 += 1
        if I2(Lhet({u: 1})) != Lhet(I2({u: 1})):
            fail4 += 1
            if fail4 <= 2: print('(4) I2 L u != L I2 u for u =', repr(u), I2(Lhet({u: 1})), Lhet(I2({u: 1})))
print('(4) words', tot4, 'commutation failures', fail4)
