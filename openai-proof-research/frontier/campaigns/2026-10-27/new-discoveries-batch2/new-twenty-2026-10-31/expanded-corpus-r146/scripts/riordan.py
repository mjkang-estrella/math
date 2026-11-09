# 337352: diameters of io-decomposable Riordan graphs of the Bell type on 2^k vertices.
# Definitions (Cheon-Jung-Kitaev-Mojallal arXiv:1710.04604v2, Def. 2.4 and eq. (4); Jung arXiv:1901.11156 eq. (9), Lemma 2.1):
#   B = B(g, zg) binary Bell matrix with b_00 = 1 and binary A-sequence (1, a1, a2, ...):
#     b_{i+1,0}   = a1 b_{i,0} + a2 b_{i,1} + ... + a_{i+1} b_{i,i}
#     b_{i+1,j+1} = b_{i,j} + a1 b_{i,j+1} + ... + a_{i-j} b_{i,i}        (mod 2)
#   G_n: vertices 1..n, for i > j >= 1: i ~ j iff b_{i-2, j-1} = 1.
#   io-decomposable (Lemma 2.1 of Jung = Thm 4.6 of CJKM): A-sequence (1, 1, a2, a2, a4, a4, ...).
#   Catalan graph CG_n = G_n(C, zC): A-sequence all ones (C = 1/(1 - zC)).
import sys, itertools, json, collections

def bell_matrix(a, rows):
    # a[0] = 1, a[1..]; returns b as list of lists (lower triangular, row i has i+1 entries)
    b = [[1]]
    for i in range(rows - 1):
        r = b[i]
        new = [0] * (i + 2)
        s = 0
        for t in range(i + 1):
            s ^= a[t + 1] & r[t]
        new[0] = s
        for j in range(i + 1):
            s = r[j]
            for t in range(1, i - j + 1):
                s ^= a[t] & r[j + t]
            new[j + 1] = s
        b.append(new)
    return b

def graph(a, n):
    b = bell_matrix(a, max(n - 1, 1))
    adj = [0] * (n + 1)  # bitmask adjacency, vertices 1..n
    for i in range(2, n + 1):
        for j in range(1, i):
            if b[i - 2][j - 1]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
    return adj

def diameter(adj, n):
    full = ((1 << (n + 1)) - 1) ^ 1
    best = 0
    for s in range(1, n + 1):
        seen = 1 << s; front = 1 << s; d = 0
        while seen != full:
            nxt = 0
            f = front
            while f:
                low = f & -f; v = low.bit_length() - 1; f ^= low
                nxt |= adj[v]
            nxt &= ~seen
            if not nxt:
                return None  # disconnected
            seen |= nxt; front = nxt; d += 1
        best = max(best, d)
    return best

def io_sequences(n):
    # entries a_0..a_{n-2}; a_0 = a_1 = 1, a_{2j} = a_{2j+1}
    L = n - 1
    free = list(range(2, L, 2))
    for bits in itertools.product((0, 1), repeat=len(free)):
        a = [0] * L
        a[0] = a[1] = 1
        for p, v in zip(free, bits):
            a[p] = v
            if p + 1 < L:
                a[p + 1] = v
        yield a

def degree_sequence(adj, n):
    return sorted(bin(adj[v]).count('1') for v in range(1, n + 1))

def wl_hash(adj, n, rounds=6):
    col = {v: bin(adj[v]).count('1') for v in range(1, n + 1)}
    for _ in range(rounds):
        sig = {}
        for v in range(1, n + 1):
            nb = sorted(col[u] for u in range(1, n + 1) if adj[v] >> u & 1)
            sig[v] = (col[v], tuple(nb))
        keys = sorted(set(sig.values()))
        idx = {k: i for i, k in enumerate(keys)}
        col = {v: idx[sig[v]] for v in sig}
    return tuple(sorted(collections.Counter(col.values()).items())), tuple(sorted(col.values()))

def isomorphic(adjA, adjB, n):
    # backtracking with degree + WL refinement colours
    def colours(adj):
        col = {v: bin(adj[v]).count('1') for v in range(1, n + 1)}
        for _ in range(n):
            sig = {v: (col[v], tuple(sorted(col[u] for u in range(1, n + 1) if adj[v] >> u & 1))) for v in col}
            keys = sorted(set(sig.values())); idx = {k: i for i, k in enumerate(keys)}
            new = {v: idx[sig[v]] for v in sig}
            if len(set(new.values())) == len(set(col.values())):
                col = new; break
            col = new
        return col
    cA, cB = colours(adjA), colours(adjB)
    if sorted(cA.values()) != sorted(cB.values()):
        return False
    order = sorted(range(1, n + 1), key=lambda v: (sum(1 for u in range(1, n + 1) if cA[u] == cA[v]), -bin(adjA[v]).count('1')))
    m = {}; used = set()
    def ok(v, w):
        for u, x in m.items():
            if ((adjA[v] >> u) & 1) != ((adjB[w] >> x) & 1):
                return False
        return True
    def bt(i):
        if i == n:
            return True
        v = order[i]
        for w in range(1, n + 1):
            if w in used or cB[w] != cA[v] or not ok(v, w):
                continue
            m[v] = w; used.add(w)
            if bt(i + 1):
                return True
            del m[v]; used.discard(w)
        return False
    return bt(0)

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'check':
        # reproduce printed matrices: A(CG6) (CJKM v2 Fig. 3) row 1 = 0 1 1 0 1 0
        adj = graph([1] * 10, 6)
        rows = [[(adj[i] >> j) & 1 for j in range(1, 7)] for i in range(1, 7)]
        print('A(CG6)=', rows)
        # Jung Example 2.7: CG8^r = G8(1, z+z^2): reversal of CG8
        adj8 = graph([1] * 10, 8)
        rev = [[(adj8[9 - i] >> (9 - j)) & 1 for j in range(1, 9)] for i in range(1, 9)]
        print('A(CG8^r)=', rev)
        for n in range(2, 101):
            d = diameter(graph([1] * n, n), n)
            if n in (44, 45, 46, 47, 48, 78, 88) or n & (n - 1) == 0 or n in (2**k - 1 for k in range(2, 8)):
                print('n', n, 'diam CG', d)
        # Jung counterexample to Conj 1: A(z) = sum_{i=0}^{15} z^i
        a = [1] * 16 + [0] * 100
        print('Jung A=1+..+z^15:', [(n, diameter(graph(a, n), n)) for n in (44, 45, 46, 47, 48, 78, 79, 80, 87, 88, 89, 90, 91)])
    elif mode == 'all':
        k = int(sys.argv[2]); n = 2 ** k
        cg = graph([1] * n, n)
        dist = collections.Counter(); hits = []
        for a in io_sequences(n):
            adj = graph(a, n)
            d = diameter(adj, n)
            dist[d] += 1
            if d is not None and d >= k:
                hits.append(a)
        print(json.dumps({'k': k, 'n': n, 'count': sum(dist.values()), 'diam_distribution': dict(sorted(dist.items(), key=lambda x: (x[0] is None, x[0]))), 'diam_ge_k': len(hits)}))
        for a in hits:
            adj = graph(a, n)
            print('A-seq', ''.join(map(str, a)), 'diam', diameter(adj, n), 'isoCG', isomorphic(adj, cg, n), 'degseq_eq', degree_sequence(adj, n) == degree_sequence(cg, n))
    elif mode == 'tail':
        # first 16 entries all ones (Jung Thm 3.3 complement); k given; free bits beyond index 15
        k = int(sys.argv[2]); n = 2 ** k; L = n - 1
        cg = graph([1] * n, n)
        free = list(range(16, L, 2))
        dist = collections.Counter(); hits = []
        for bits in itertools.product((0, 1), repeat=len(free)):
            a = [1] * 16 + [0] * (L - 16)
            for p, v in zip(free, bits):
                a[p] = v
                if p + 1 < L: a[p + 1] = v
            adj = graph(a, n); d = diameter(adj, n); dist[d] += 1
            if d == k: hits.append(a)
        print(json.dumps({'k': k, 'free_bits': len(free), 'diam_distribution': dict(dist), 'diam_eq_k': len(hits)}))
        for a in hits[:50]:
            adj = graph(a, n)
            print('A-seq', ''.join(map(str, a)), 'isoCG', isomorphic(adj, cg, n))
