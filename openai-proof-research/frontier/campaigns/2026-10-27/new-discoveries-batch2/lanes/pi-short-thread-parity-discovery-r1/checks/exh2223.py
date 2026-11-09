"""Definitive exhaustive validation of the mixed-class generator at n=21,22.
Enumerates ALL n-vertex trees via leaf extension (ground truth), filters
Q11.4 class + twin-free (independent checker), compares canon-key sets both
ways against gen_twinfree_pieces + is_twinfree."""
import sys, time, collections
sys.path.insert(0, '.')
from cycles_solver import canon
from crosscheck_gen import is_twinfree_indep
from genpieces import gen_twinfree_pieces, is_twinfree

t0 = time.time()
N = 22

def key_of(n, edges):
    return canon(n, edges, tuple(0 for _ in range(n)))

prev = {key_of(1, []): (1, [])}
for n in range(2, N):
    cur = {}
    for pn, pe in prev.values():
        for v in range(pn):
            ne = list(pe) + [(v, pn)]
            cur.setdefault(key_of(n, ne), (n, ne))
    prev = cur
    print(f"level {n}: {len(cur)} ({time.time()-t0:.0f}s)", flush=True)

pieces = gen_twinfree_pieces(N)
gen_tf = {k: (n, e) for k, (n, e) in pieces.items() if is_twinfree(n, e)}
gen21 = set(k for k, (n, e) in gen_tf.items() if n == N - 1)
gen22 = set(k for k, (n, e) in gen_tf.items() if n == N)
print(f"gen tf: n={N-1}: {len(gen21)}  n={N}: {len(gen22)}  ({time.time()-t0:.0f}s)", flush=True)

def scan(n, genkeys):
    indep = {}
    for pn, pe in prev.values():
        for v in range(pn):
            ne = list(pe) + [(v, pn)]
            if len(ne) + 1 != n:
                continue
            deg = [0] * n
            for a, b in ne:
                deg[a] += 1
                deg[b] += 1
            # class check: internal threads <= 2, leaf threads <= 3
            ok = True
            for s in range(n):
                if deg[s] == 2:
                    continue
                for t in adj_ne(ne, n, s):
                    x = t; prv = s; L = 1
                    while deg[x] == 2:
                        nxt = [y for y in adj_ne(ne, n, x) if y != prv][0]
                        prv = x; x = nxt; L += 1
                    internal = deg[s] >= 3 and deg[x] >= 3
                    if L > (2 if internal else 3):
                        ok = False; break
                if not ok:
                    break
            if not ok:
                continue
            if is_twinfree_indep(n, ne):
                st = tuple(3 if deg[i] == 1 else 0 for i in range(n))
                indep[canon(n, ne, st)] = ne
    miss = [k for k in indep if k not in genkeys]
    extra = [k for k in genkeys if k not in indep]
    print(f"n={n}: indep-tf={len(indep)}  gen-tf={len(genkeys)}  gen-missing={len(miss)}  gen-bogus={len(extra)}", flush=True)
    for k in miss[:3]:
        print("  MISSING:", indep[k])
    return len(miss), len(extra)

def adj_ne(edges, n, x):
    for a, b in edges:
        if a == x: yield b
        if b == x: yield a

scan(N - 1, gen21)
scan(N, gen22)
print(f"total {time.time()-t0:.0f}s", flush=True)
