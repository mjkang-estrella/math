"""Exhaustive check at n=21 and n=22: enumerate ALL trees via leaf extension,
filter class + twin-free, compare against gen_twinfree_pieces."""
import sys, time
sys.path.insert(0, '.')
from cycles_solver import canon
from crosscheck_gen import threads_ok, is_twinfree_indep
from genpieces import gen_twinfree_pieces, is_twinfree

t0 = time.time()
N = int(sys.argv[1]) if len(sys.argv) > 1 else 22

def key_of(n, edges):
    return canon(n, edges, tuple(0 for _ in range(n)))

prev = {key_of(1, []): (1, [])}
for n in range(2, N):
    cur = {}
    for pn, pe in prev.values():
        for v in range(pn):
            ne = list(pe) + [(v, pn)]
            k = key_of(n, ne)
            if k not in cur:
                cur[k] = (n, ne)
    prev = cur
    print(f"level {n}: {len(cur)} ({time.time()-t0:.0f}s)", flush=True)

pieces = gen_twinfree_pieces(N)
genkeys_21 = set(k for k, (n, e) in pieces.items() if n == N - 1)
genkeys_22 = set(k for k, (n, e) in pieces.items() if n == N)

def scan(n, genkeys):
    missing = []
    tfcnt = 0
    for pn, pe in prev.values():
        for v in range(pn):
            ne = list(pe) + [(v, pn)]
            if len(ne) + 1 != n:
                continue
            if not threads_ok(n, ne):
                continue
            st = tuple(3 if sum(1 for a, b in ne if a == i or b == i) == 1 else 0 for i in range(n))
            key = canon(n, ne, st)
            if is_twinfree_indep(n, ne):
                tfcnt += 1
                if key not in genkeys:
                    missing.append((n, ne))
    return tfcnt, missing

t21, m21 = scan(N - 1, genkeys_21)
print(f"n={N-1}: indep tf={t21}  gen tf={sum(1 for n,e in pieces.values() if n==N-1)}  missing={len(m21)}", flush=True)
for m in m21[:5]:
    print("  MISSING", m)
t22, m22 = scan(N, genkeys_22)
print(f"n={N}: indep tf={t22}  gen tf={sum(1 for n,e in pieces.values() if n==N)}  missing={len(m22)}", flush=True)
for m in m22[:5]:
    print("  MISSING", m)
