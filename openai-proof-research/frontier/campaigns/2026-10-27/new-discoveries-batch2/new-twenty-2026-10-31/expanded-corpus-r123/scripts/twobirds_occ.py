# 346465: search occurrences of two-birds formulas T_k in a given binary word prefix,
# bounded image lengths |h(A_i)| <= L.  Usage: word in {tm, fib, ...}, k, L, N
import sys
def tm(N): return ''.join(str(bin(i).count('1') % 2) for i in range(N))
def fixed(m, N, a='0'):
    w = a
    while len(w) < N: w = ''.join(m[c] for c in w)
    return w[:N]
WORDS = {'tm': lambda N: tm(N), 'fib': lambda N: fixed({'0': '01', '1': '0'}, N),
         'pd': lambda N: fixed({'0': '01', '1': '00'}, N)}
def occurrences(w, k, L, maxlen):
    # factor set up to maxlen
    F = set()
    for i in range(len(w)):
        for j in range(i + 1, min(len(w), i + maxlen) + 1): F.add(w[i:j])
    found = []
    # DFS on frag1 = u1..u_{k-1} u_k u_{k-1}..u1 as a factor: choose u1..u_{k-1} then u_k
    def rec(prefix_parts, s):
        i = len(prefix_parts)
        if i == k - 1:
            for lk in range(1, L + 1):
                for uk in set(x[len(s):len(s) + lk] for x in [None] if False) or []: pass
            # enumerate u_k as any word with s+u_k+mirror in F
            for lk in range(1, L + 1):
                cand = set()
                for f in Fby[len(s) + lk]:
                    if f.startswith(s): cand.add(f[len(s):])
                for uk in cand:
                    f1 = s + uk + ''.join(prefix_parts[::-1])
                    if f1 in F:
                        Q = prefix_parts[1:][::-1]  # u_{k-1}..u_2
                        f2 = uk + ''.join(Q) + prefix_parts[0] + ''.join(Q[::-1]) + uk
                        if f2 in F: found.append(tuple(prefix_parts) + (uk,)); return True
            return False
        for l in range(1, L + 1):
            cand = set(f[len(s):] for f in Fby.get(len(s) + l, ()) if f.startswith(s))
            for u in cand:
                if rec(prefix_parts + [u], s + u): return True
        return False
    Fby = {}
    for f in F: Fby.setdefault(len(f), set()).add(f)
    rec([], '')
    return found
if __name__ == '__main__':
    name, k, L, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    w = WORDS[name](N)
    r = occurrences(w, k, L, (2 * k - 1) * L)
    print(name, 'k', k, 'L', L, 'N', N, 'occurrence' if r else 'none', r[:1], flush=True)
