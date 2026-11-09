# 337352: bit-parallel Bell-matrix rows; exhaustive sweep of io-decomposable Bell-type G_{2^K}
# whose first 2^(K-1)-1 A-entries are all ones (forced by the induction; see SUMMARY.md),
# optionally restricted to a chunk of the free bits.  Cross-checked against scripts/riordan.py.
import sys, json, itertools, collections

def rows_from_a(a, nrows):
    # R[i] bitmask, bit j = b_{i,j}.  b_{i+1,j+1} = XOR_{t>=0} a_t b_{i,j+t};  b_{i+1,0} = XOR_{t>=0} a_{t+1} b_{i,t}
    R = [1]
    A1 = 0
    for t in range(1, len(a)):
        if a[t]: A1 |= 1 << (t - 1)
    for i in range(nrows - 1):
        r = R[i]
        s = 0
        for t in range(0, i + 1):
            if a[t]: s ^= r >> t
        s &= (1 << (i + 1)) - 1
        b0 = bin(r & A1).count('1') & 1
        R.append((s << 1) | b0)
    return R

def adjacency(R, n):
    adj = [0] * (n + 1)
    for i in range(2, n + 1):
        row = R[i - 2] << 1          # bit j (1-based) = b_{i-2, j-1}
        row &= (1 << i) - 2           # j in 1..i-1
        adj[i] |= row
        j = row
        while j:
            low = j & -j; v = low.bit_length() - 1; j ^= low
            adj[v] |= 1 << i
    return adj

def ecc_all(adj, n, cutoff):
    # returns diameter (or cutoff+1 early-exit marker >cutoff) ; disconnected -> None
    full = ((1 << (n + 1)) - 1) ^ 1
    best = 0
    for s in range(1, n + 1):
        seen = 1 << s; front = seen; d = 0
        while seen != full:
            nxt = 0; f = front
            while f:
                low = f & -f; v = low.bit_length() - 1; f ^= low
                nxt |= adj[v]
            nxt &= ~seen
            if not nxt: return None
            seen |= nxt; front = nxt; d += 1
        if d > best:
            best = d
            if best > cutoff: return best
    return best

def make_a(n, prefix_ones, bits, free):
    L = n - 1
    a = [1] * prefix_ones + [0] * (L - prefix_ones)
    for p, v in zip(free, bits):
        a[p] = v
        if p + 1 < L: a[p + 1] = v
    return a

if __name__ == '__main__':
    K = int(sys.argv[1]); n = 2 ** K; L = n - 1
    pref = 2 ** (K - 1)            # entries 0..2^(K-1)-1 ones (index 2^(K-1)-1 is paired with 2^(K-1)-2)
    free = list(range(pref, L, 2))
    chunk = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    nchunks = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    total = 2 ** len(free)
    lo = total * chunk // nchunks; hi = total * (chunk + 1) // nchunks
    dist = collections.Counter(); hits = []
    for idx in range(lo, hi):
        bits = [(idx >> (len(free) - 1 - q)) & 1 for q in range(len(free))]
        a = make_a(n, pref, bits, free)
        adj = adjacency(rows_from_a(a, n - 1), n)
        d = ecc_all(adj, n, K - 1)
        key = d if (d is None or d <= K - 1) else '>=K'
        dist[key] += 1
        if key == '>=K': hits.append(''.join(map(str, a)))
    print(json.dumps({'K': K, 'n': n, 'free_bits': len(free), 'range': [lo, hi], 'dist': {str(k): v for k, v in dist.items()}, 'hits': hits}))
