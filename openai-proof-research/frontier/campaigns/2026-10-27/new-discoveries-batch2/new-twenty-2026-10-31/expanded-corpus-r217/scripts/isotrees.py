# All free trees of order n (AHU canonical forms, grown by leaf addition), solved for the total
# isolation game (rules as in isogame.py). Checks Henning-Rall Conjecture 1 on trees.
# usage: isotrees.py NMIN NMAX [START END]   (START/END slice the order-NMAX tree list)
import sys, importlib.util, pathlib
spec = importlib.util.spec_from_file_location('isogame', str(pathlib.Path(sys.argv[0]).resolve().parent / 'isogame.py'))
iso = importlib.util.module_from_spec(spec); spec.loader.exec_module(iso)

def centers(n, nb):
    deg = [len(nb[v]) for v in range(n)]
    leaves = [v for v in range(n) if deg[v] <= 1]; rem = n
    while rem > 2:
        new = []
        for v in leaves:
            rem -= 1
            for u in nb[v]:
                deg[u] -= 1
                if deg[u] == 1: new.append(u)
        leaves = new
    return leaves

def ahu(v, p, nb):
    return '(' + ''.join(sorted(ahu(u, v, nb) for u in nb[v] if u != p)) + ')'

def canon(n, nb):
    return min(ahu(c, -1, nb) for c in centers(n, nb))

def grow(nmax):
    levels = {1: {canon(1, [[]]): [[]]}}
    for n in range(2, nmax + 1):
        cur = {}
        for nb in levels[n - 1].values():
            for v in range(n - 1):
                nb2 = [list(x) for x in nb] + [[v]]
                nb2[v].append(n - 1)
                c = canon(n, nb2)
                if c not in cur: cur[c] = nb2
        levels[n] = cur
    return levels

if __name__ == '__main__':
    sys.setrecursionlimit(10000)
    nmin, nmax = int(sys.argv[1]), int(sys.argv[2])
    a = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    b = int(sys.argv[4]) if len(sys.argv) > 4 else 10**9
    levels = grow(nmax)
    for n in range(nmin, nmax + 1):
        trees = list(levels[n].values())
        if n == nmax: trees = trees[a:b]
        worst = 0; viol = 0; ex = None
        for nb in trees:
            adj = [sum(1 << u for u in nb[v]) for v in range(n)]
            d, s = iso.solve(n, adj)
            if d > worst: worst, ex = d, nb
            if 3 * d > 2 * n: viol += 1; print('VIOLATION', n, nb, d, s, flush=True)
        print(f'trees n={n} count={len(levels[n])} tested={len(trees)} max D-value={worst} bound={2*n/3:.2f} violations={viol} example={ex}', flush=True)
