"""335271: analyse found tight k-in-out graphs (from outputs/kinout/*.json): Hamiltonian path counts per start,
pairing permutation, and for a=0 the integer determinants of In/Out incidence minors.
usage: kinout_analyse.py FILE1.json [FILE2.json ...]"""
import sys, json, itertools


def det(M):
    M = [list(map(int, r)) for r in M]
    n = len(M)
    if n == 0:
        return 1
    # Bareiss
    sign = 1
    prev = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for i in range(k + 1, n):
                if M[i][k] != 0:
                    M[k], M[i] = M[i], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[-1][-1]


for f in sys.argv[1:]:
    d = json.load(open(f))
    for sol in d['found_first']:
        w = sol['pattern']
        n = len(w)
        succ = [[] for _ in range(n)]
        for u, v in sol['arcs']:
            succ[u].append(v)
        full = (1 << n) - 1
        inc = [v for v in range(n) if w[v] in 'IB']
        cnt = {}
        for s0 in inc:
            stack = [(s0, 1 << s0)]
            while stack:
                v, m = stack.pop()
                if m == full:
                    cnt[(s0, v)] = cnt.get((s0, v), 0) + 1
                    continue
                for t in succ[v]:
                    if not (m >> t) & 1:
                        stack.append((t, m | (1 << t)))
        info = {'pattern': w, 'path_counts': {f'{s}->{t}': c for (s, t), c in sorted(cnt.items()) if w[t] in 'OB'}}
        if 'I' not in w:
            B = [v for v in range(n) if w[v] == 'B']
            N = [v for v in range(n) if w[v] == 'N']
            Ain = [[1 if x in succ[b] else 0 for x in N] for b in B]
            Aout = [[1 if b in succ[x] else 0 for b in B] for x in N]
            dets = {}
            for (s, t), c in cnt.items():
                if w[t] != 'B':
                    continue
                ti, si = B.index(t), B.index(s)
                d1 = det([r for i, r in enumerate(Ain) if i != ti])
                d2 = det([[r[j] for j in range(len(B)) if j != si] for r in Aout])
                dets[f'{s}->{t}'] = (d1, d2)
            info['minor_dets'] = dets
        print(json.dumps(info))
