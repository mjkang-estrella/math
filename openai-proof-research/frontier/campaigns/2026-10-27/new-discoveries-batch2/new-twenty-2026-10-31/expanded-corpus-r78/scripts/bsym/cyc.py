# Existence of cyclic sequences v_0..v_{n-1} in F_2^b with every b cyclically consecutive vectors
# linearly independent (equivalent, by the cluster argument, to a linear MDS (n,2b)_2 b-symbol code).
# WLOG (GL_b(F_2) acts transitively on ordered bases) v_0..v_{b-1} = e_0..e_{b-1}.
import sys, json
def indep(vs):
    basis = []
    for v in vs:
        for bv in basis:
            v = min(v, v ^ bv)
        if v == 0: return False
        basis.append(v)
    return True
def search(b, n, want_all=False):
    seq = [1 << i for i in range(b)]
    count = 0; first = None
    nodes = 0
    def rec():
        nonlocal count, first, nodes
        nodes += 1
        L = len(seq)
        if L == n:
            # check wrap windows starting at n-b+1 .. n-1
            for s in range(n - b + 1, n):
                w = [seq[(s + j) % n] for j in range(b)]
                if not indep(w): return False
            count += 1
            if first is None: first = list(seq)
            return not want_all
        prev = seq[L - b + 1:]
        for v in range(1, 1 << b):
            if indep(prev + [v]):
                # early wrap pruning: windows that include positions >= n-? computed at the end
                seq.append(v)
                if rec(): return True
                seq.pop()
        return False
    rec()
    return count, first, nodes
b = int(sys.argv[1]); ns = [int(x) for x in sys.argv[2].split(',')]
for n in ns:
    c, f, nodes = search(b, n)
    print(json.dumps({'q': 2, 'b': b, 'n': n, 'exists': c > 0, 'example': f, 'nodes': nodes}), flush=True)
