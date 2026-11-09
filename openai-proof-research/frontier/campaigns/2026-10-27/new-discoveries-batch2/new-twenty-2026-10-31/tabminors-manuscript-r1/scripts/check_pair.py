#!/usr/bin/env python3
"""Small independent check (manuscript lane): jeu de taquin deletion written from the
source text, weighted level-by-level multisets of k-minors for T1 and T2, the hook
weight formula of Lemma 2 on both hooks, and agreement with the Lean literals A8/B8.
Pure Python, no Lean. Usage: check_pair.py <TabMinors.lean>"""
import sys, json, re, math
from itertools import combinations
from collections import Counter

def is_syt(T, n):
    if any(len(r) == 0 for r in T): return False
    if any(len(T[i+1]) > len(T[i]) for i in range(len(T)-1)): return False
    if any(r[j] >= r[j+1] for r in T for j in range(len(r)-1)): return False
    if any(T[i][j] >= T[i+1][j] for i in range(len(T)-1) for j in range(len(T[i+1]))): return False
    return sorted(x for r in T for x in r) == list(range(1, n+1))

def delete(T, m):
    """Source rule: delete cell m; while a cell lies right of or below the gap, slide the
    smaller of them into the gap; remove the final outer corner; subtract 1 above m."""
    T = [list(r) for r in T]
    i = next(a for a, r in enumerate(T) if m in r); j = T[i].index(m)
    while True:
        right = T[i][j+1] if j+1 < len(T[i]) else None
        below = T[i+1][j] if i+1 < len(T) and j < len(T[i+1]) else None
        if right is None and below is None: break
        if below is None or (right is not None and right < below):
            T[i][j] = right; j += 1
        else:
            T[i][j] = below; i += 1
    del T[i][j]
    T = [r for r in T if r]
    return tuple(tuple(x-1 if x > m else x for x in r) for r in T)

def minors(T, k):
    level = Counter({T: 1}); n = sum(map(len, T))
    for s in range(k):
        nxt = Counter()
        for U, c in level.items():
            for m in range(1, n-s+1):
                V = delete(U, m); assert is_syt(V, n-s-1); nxt[V] += c
        level = nxt
    return level

def hook_word(T):
    arm = set(T[0][1:]); n = sum(map(len, T))
    return ''.join('A' if t in arm else 'L' for t in range(2, n+1))

def hook_from_word(w):
    arm = [t+2 for t, a in enumerate(w) if a == 'A']; leg = [t+2 for t, a in enumerate(w) if a == 'L']
    return tuple([tuple([1]+arm)] + [(x,) for x in leg])

def lemma2(w, k):
    N = len(w); out = Counter()
    for P in combinations(range(1, N+1), N-k):
        out[hook_from_word(''.join(w[p-1] for p in P))] += math.factorial(k)*min(P)
    return out

def lean_list(src, name):
    m = re.search(r'def ' + name + r' : List \(Tab × ℕ\) := (\[.*\])\n', src)
    data = json.loads(m.group(1).replace('(', '[').replace(')', ']'))
    return Counter({tuple(tuple(r) for r in t): c for t, c in data})

if sys.argv[1] == '--c5':
    # n = k + 5 hook pair (k = 11, n = 16): exact deletion DP plus the Lemma 2 formula.
    T = ((1, 2, 3, 4, 5, 9, 10, 11, 12, 13, 16), (6,), (7,), (8,), (14,), (15,))
    U = ((1, 4, 5, 6, 7, 8, 12, 13, 14, 15), (2,), (3,), (9,), (10,), (11,), (16,))
    MT, MU = minors(T, 11), minors(U, 11)
    r = dict(T_syt=is_syt(T, 16), U_syt=is_syt(U, 16), distinct=T != U, equal_mM11=MT == MU,
             total=sum(MT.values()), total_expected=math.factorial(16)//math.factorial(5),
             lemma2_T=lemma2(hook_word(T), 11) == MT, lemma2_U=lemma2(hook_word(U), 11) == MU)
    r['PASS'] = all(v for v in r.values() if isinstance(v, bool)) and r['total'] == r['total_expected']
    print(json.dumps(r)); sys.exit(0)

T1 = ((1, 5, 7, 8, 12), (2,), (3,), (4,), (6,), (9,), (10,), (11,))
T2 = ((1, 2, 3, 7, 10, 11), (4,), (5,), (6,), (8,), (9,), (12,))
src = open(sys.argv[1], encoding='utf8').read()
r = {}
r['T1_syt'], r['T2_syt'], r['distinct'] = is_syt(T1, 12), is_syt(T2, 12), T1 != T2
M1, M2 = minors(T1, 8), minors(T2, 8)
r['equal_mM8'] = M1 == M2
r['total_each'] = sum(M1.values())
r['total_expected'] = math.factorial(12)//math.factorial(4)
r['distinct_minors'] = len(M1)
r['lemma2_T1'] = lemma2(hook_word(T1), 8) == M1
r['lemma2_T2'] = lemma2(hook_word(T2), 8) == M2
r['lean_A8_matches'] = lean_list(src, 'A8') == M1
r['lean_B8_matches'] = lean_list(src, 'B8') == M2
r['differ_for_k_1_to_7'] = all(minors(T1, k) != minors(T2, k) for k in range(1, 8))
fig = ((1,2,3,4,5),(6,7,8,9,18),(10,11,12,17),(13,16),(14,),(15,))
r['source_figure_T_minus_8'] = delete(fig, 8) == ((1,2,3,4,5),(6,7,8,16,17),(9,10,11),(12,15),(13,),(14,))
r['counts'] = sorted(([list(map(list, t)), c] for t, c in M1.items()), key=lambda x: -x[1])
r['PASS'] = all(v for k, v in r.items() if isinstance(v, bool)) and r['total_each'] == r['total_expected']
print(json.dumps(r))
