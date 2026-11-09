"""Search for counterexamples to Das, arXiv:2112.00442v3, Conjecture 5.1.

A: zero-diagonal sign pattern over {+,-,0}.  AP-irreducible := D(A) strongly connected,
every row and column contains '+', and B_A = A^+ - (A^-)^T irreducible (arc i->j iff
a_ij='+' or a_ji='-').  Minimal := zeroing any single nonzero entry destroys AP-irreducibility.
Conjecture: minimal => at most 2n-2 nonzero entries.
Usage: apirr.py exhaustive N  |  apirr.py random N TRIALS SEED
"""
import sys, random, itertools, json


def strong(n, arcs):
    out = [[] for _ in range(n)]; inn = [[] for _ in range(n)]
    for i, j in arcs:
        out[i].append(j); inn[j].append(i)
    for adj in (out, inn):
        seen = {0}; st = [0]
        while st:
            v = st.pop()
            for w in adj[v]:
                if w not in seen:
                    seen.add(w); st.append(w)
        if len(seen) < n:
            return False
    return True


def ap_irr(n, A):
    plus = [(i, j) for (i, j), s in A.items() if s > 0]
    if {i for i, _ in plus} != set(range(n)) or {j for _, j in plus} != set(range(n)):
        return False
    if not strong(n, list(A)):
        return False
    B = plus + [(j, i) for (i, j), s in A.items() if s < 0]
    return strong(n, B)


def minimal(n, A):
    for k in list(A):
        s = A.pop(k)
        ok = ap_irr(n, A)
        A[k] = s
        if ok:
            return False
    return True


def reduce_random(n, A, rng):
    keys = list(A); rng.shuffle(keys)
    changed = True
    while changed:
        changed = False
        for k in [k for k in keys if k in A]:
            s = A.pop(k)
            if ap_irr(n, A):
                changed = True
            else:
                A[k] = s
    return A


def show(n, A):
    return [''.join({1: '+', -1: '-', 0: '0'}[A.get((i, j), 0)] for j in range(n)) for i in range(n)]


if __name__ != '__main__':
    pass
elif sys.argv[1] == 'exhaustive':
    n = int(sys.argv[2])
    cells = [(i, j) for i in range(n) for j in range(n) if i != j]
    best = 0; hits = []
    for vals in itertools.product((0, 1, -1), repeat=len(cells)):
        A = {c: v for c, v in zip(cells, vals) if v}
        if len(A) <= 2 * n - 2 and len(A) <= best:
            continue
        if ap_irr(n, A) and minimal(n, A):
            if len(A) > best:
                best = len(A)
            if len(A) > 2 * n - 2:
                hits.append(show(n, A))
                print('COUNTEREXAMPLE', show(n, A), flush=True)
                break
    print(json.dumps({'n': n, 'max_nonzeros_minimal': best, 'bound': 2 * n - 2, 'hits': hits[:3]}))
else:
    n, trials, seed = map(int, sys.argv[2:5])
    rng = random.Random(seed)
    cells = [(i, j) for i in range(n) for j in range(n) if i != j]
    best = 0; ex = None
    for t in range(trials):
        dens = rng.uniform(0.3, 1.0); pp = rng.uniform(0.2, 0.8)
        A = {c: (1 if rng.random() < pp else -1) for c in cells if rng.random() < dens}
        if not ap_irr(n, A):
            continue
        A = reduce_random(n, A, rng)
        if len(A) > best:
            best = len(A); ex = show(n, A)
        if len(A) > 2 * n - 2:
            print('COUNTEREXAMPLE', n, len(A), show(n, A), flush=True)
            break
    print(json.dumps({'n': n, 'trials': trials, 'max_found': best, 'bound': 2 * n - 2, 'example': ex}))
