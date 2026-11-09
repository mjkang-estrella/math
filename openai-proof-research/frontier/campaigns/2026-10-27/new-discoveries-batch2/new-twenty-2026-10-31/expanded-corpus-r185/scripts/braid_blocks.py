"""MathDB 342653 (Alekseev-Mamedov Conj. 'Wreathlike'): two e-homogeneous braid words for the same braid
have equal letter counts in each homogeneous block.
Exhaustive check: all e-homogeneous words of length <= L over generators sigma_i^{e_i}, i=1..n-1,
braids identified by the (faithful) Artin action on the free group F_n.
Usage: braid_blocks.py e_string L     e.g.  '++-+' 9
We enumerate words by BFS over braids (dedup by image), storing for each braid image the set of block-count vectors.
Since homogeneous words are geodesic (source Thm), all words of one braid have the same length, so BFS by length suffices.
"""
import sys
es = sys.argv[1]; L = int(sys.argv[2])
e = [1 if c == '+' else -1 for c in es]
m = len(e); n = m + 1
# blocks
blk = []; b = 0
for i in range(m):
    if i > 0 and e[i] != e[i - 1]: b += 1
    blk.append(b)
nb = b + 1

def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x: out.pop()
        else: out.append(x)
    return tuple(out)

def inv(w): return tuple(-x for x in reversed(w))

def act(img, i, s):
    # img: tuple of images of generators x_1..x_n (as words in letters +-1..+-n) for current braid beta (left-to-right composition)
    # right-multiply beta by sigma_i^s : new phi = phi_beta o phi_sigma ? We use the convention: braid acts on the right, word w=a1...ak
    # gives automorphism phi_w = phi_{a1} o ... o phi_{ak} applied as substitution. Faithfulness holds for either consistent convention.
    # sigma_i: x_i -> x_i x_{i+1} x_i^{-1}, x_{i+1} -> x_i ; inverse: x_i -> x_{i+1}, x_{i+1} -> x_{i+1}^{-1} x_i x_{i+1}
    # new images: phi_new(x_j) = phi_beta(phi_sigma(x_j)) (substitute images of beta into sigma's formula)
    a, c = img[i - 1], img[i]
    if s == 1:
        na = red(a + c + inv(a)); nc = a
    else:
        na = c; nc = red(inv(c) + a + c)
    lst = list(img); lst[i - 1] = na; lst[i] = nc
    return tuple(lst)

start = tuple((j,) for j in range(1, n + 1))
level = {start: {tuple([0] * nb)}}
bad = 0
for length in range(1, L + 1):
    new = {}
    for img, cs in level.items():
        for i in range(1, m + 1):
            ni = act(img, i, e[i - 1])
            ncs = set()
            for cv in cs:
                v = list(cv); v[blk[i - 1]] += 1; ncs.add(tuple(v))
            if ni in new: new[ni] |= ncs
            else: new[ni] = ncs
    viol = [(img, cs) for img, cs in new.items() if len(cs) > 1]
    print('length', length, 'braids', len(new), 'violations', len(viol), flush=True)
    if viol:
        img, cs = viol[0]; print('EXAMPLE counts', sorted(cs)); bad += 1; break
    level = new
print('e', es, 'blocks', blk, 'done; bad', bad)
