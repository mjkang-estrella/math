# Cooper-Rowland (arXiv:1307.8216v2, Contemp. Math. 633) Section 5 size-1 conjectures; MathDB 326025.
# Count non-root automorphic conjugacy classes W of F2 with |V(Gamma(W))| = 1 whose minimal words
# have length n and weight wt (= min(#a-letters, #b-letters), letters counted with inverses).
# Letters: 0=a, 1=A(a^-1), 2=b, 3=B(b^-1); inverse(x) = x^1.
# Vertices of Gamma(W): J-classes of minimal words (J = inner automorphisms + 8 permutations of L2).
# Edges: one-letter automorphisms ({y},x): y->yx, Y->Xy... (y -> y x, y^-1 -> x^-1 y^-1).
# Gamma(W) is connected (Whitehead), so |V| = 1 iff every level one-letter image of w is J-equivalent to w.
# usage: f2classes.py validate NMAX | f2classes.py count WT NMIN NMAX
import sys, itertools

INV = [1, 0, 3, 2]

def reduce_cyclic(w):
    st = []
    for x in w:
        if st and st[-1] == INV[x]: st.pop()
        else: st.append(x)
    i, j = 0, len(st) - 1
    while i < j and st[i] == INV[st[j]]: i += 1; j -= 1
    return tuple(st[i:j + 1])

# 8 permutations (signed permutations of {a,b}) as letter maps
PERMS = []
for swap in (False, True):
    for sa in (0, 1):
        for sb in (0, 1):
            m = [0] * 4
            ia, ib = (2, 0) if swap else (0, 2)
            m[0] = ia ^ sa; m[1] = INV[m[0]]
            m[2] = ib ^ sb; m[3] = INV[m[2]]
            PERMS.append(m)

def jcanon(w):
    n = len(w); best = None
    for m in PERMS:
        v = [m[x] for x in w]
        for r in range(n):
            t = tuple(v[r:] + v[:r])
            if best is None or t < best: best = t
    return best

# one-letter automorphisms: y in L2, x in L2 with x not in {y, y^-1}
ONE = []
for y in range(4):
    for x in range(4):
        if x // 2 == y // 2: continue
        img = {}
        for z in range(4):
            if z == y: img[z] = (y, x)
            elif z == INV[y]: img[z] = (INV[x], INV[y])
            else: img[z] = (z,)
        ONE.append(img)

def apply(img, w):
    out = []
    for z in w: out.extend(img[z])
    return reduce_cyclic(out)

def is_minimal(w):
    n = len(w)
    return all(len(apply(img, w)) >= n for img in ONE)

def pair_counts(w):
    # (u)_w for |u|=2: occurrences of u and u^-1 cyclically
    n = len(w); c = {}
    for i in range(n):
        u = (w[i], w[(i + 1) % n])
        ui = (INV[u[1]], INV[u[0]])
        k = min(u, ui)
        c[k] = c.get(k, 0) + 1
    def cnt(x, y):
        u = (x, y); ui = (INV[y], INV[x]); return c.get(min(u, ui), 0)
    return cnt

def thm16(w, variant):
    cnt = pair_counts(w)
    aa = cnt(0, 0); bb = cnt(2, 2)
    if variant == 'ab-aB': d = abs(cnt(0, 2) - cnt(0, 3))
    else: d = abs(cnt(0, 2) - cnt(1, 2))
    return d, aa, bb

def is_root(w, variant):
    d, aa, bb = thm16(w, variant)
    return d == aa == bb

def size_one(w):
    c = jcanon(w); n = len(w)
    for img in ONE:
        v = apply(img, w)
        if len(v) == n and jcanon(v) != c: return False
    return True

def gamma_size(w):
    # BFS on J-classes via level one-letter automorphisms (all reps of each visited class)
    n = len(w); start = jcanon(w); seen = {start}; frontier = [w]
    while frontier:
        nxt = []
        for u in frontier:
            for img in ONE:
                v = apply(img, u)
                if len(v) == n:
                    c = jcanon(v)
                    if c not in seen: seen.add(c); nxt.append(v)
        frontier = nxt
    return len(seen)

def all_cyclic_reduced(n):
    for w in itertools.product(range(4), repeat=n):
        if all(w[i] != INV[w[(i + 1) % n]] for i in range(n)) and (n > 0):
            yield w

def block_words(n, wt):
    # cyclic words with exactly wt letters from {b,B} and n-wt from {a,A}, as alternating blocks.
    # every such cyclically reduced word is a rotation of a^{e1 k1} b^{f1 m1} ... a^{er kr} b^{fr mr}
    na = n - wt
    for r in range(1, wt + 1):
        for ms in compositions(wt, r):
            for ks in compositions(na, r):
                for es in itertools.product((0, 1), repeat=r):
                    for fs in itertools.product((2, 3), repeat=r):
                        w = []
                        for i in range(r):
                            w += [es[i]] * ks[i] + [fs[i]] * ms[i]
                        w = tuple(w)
                        if all(w[i] != INV[w[(i + 1) % n]] for i in range(n)):
                            yield w

def compositions(total, parts):
    if parts == 1:
        if total >= 1: yield (total,)
        return
    for first in range(1, total - parts + 2):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest

def count(wt, n, variant='ab-aB'):
    classes = {}
    for w in block_words(n, wt):
        if not is_minimal(w): continue
        c = jcanon(w)
        if c in classes: continue
        classes[c] = (is_root(w, variant), size_one(w))
    nonroot1 = sum(1 for r, s in classes.values() if not r and s)
    return nonroot1, len(classes), sum(1 for r, s in classes.values() if r)

def conj(wt, n):
    if wt == 2: return n - 2 if n % 2 == 0 else n - 3
    if wt == 3: return 3 * n - 11
    if wt == 4:
        r = n % 4
        num = {0: 2*n**3 - 36*n**2 + 244*n - 540, 1: 2*n**3 - 36*n**2 + 241*n - 537,
               2: 2*n**3 - 36*n**2 + 244*n - 546, 3: 2*n**3 - 36*n**2 + 241*n - 537}[r]
        assert num % 6 == 0
        return num // 6
    if wt == 5:
        num = 35*n**3 - 645*n**2 + 3988*n - 8262
        return num / 6
    return None

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'validate':
        nmax = int(sys.argv[2])
        for n in range(2, nmax + 1):
            agree = {'ab-aB': 0, 'ab-Ab': 0}; tot = 0; roots = {'ab-aB': 0, 'ab-Ab': 0}
            for w in all_cyclic_reduced(n):
                tot += 1; m = is_minimal(w)
                for var in agree:
                    d, aa, bb = thm16(w, var)
                    agree[var] += (m == (d <= min(aa, bb)))
                    if m and d == aa == bb: roots[var] += 1
            print('n', n, 'cyclically reduced words', tot, 'Thm1.6 agreement', agree, 'root minimal words', roots, flush=True)
    elif mode == 'count':
        wt, a, b = map(int, sys.argv[2:5])
        var = sys.argv[5] if len(sys.argv) > 5 else 'ab-aB'
        for n in range(a, b + 1):
            got, ncls, nroot = count(wt, n, var)
            exp = conj(wt, n)
            print(f'wt={wt} n={n} nonroot size-1 classes={got} conjectured={exp} {"MISMATCH" if exp is not None and got != exp else ""} (minimal J-classes {ncls}, root {nroot})', flush=True)
