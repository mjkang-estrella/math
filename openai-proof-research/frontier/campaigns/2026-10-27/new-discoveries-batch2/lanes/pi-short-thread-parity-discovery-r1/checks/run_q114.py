"""Grundy computation over all twin-free Q11.4-class pieces <= 22 vertices.
Violation iff g > 1 or g != E mod 2 (E = piece edges = markable edges of the
realized tree), matching the source's parsolve2 test (g%2)!=(E%2)||g>1.
Sharded over cores; writes results_q114.json + violations list."""
import sys, time, json, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from multiprocessing import Pool
from genpieces import gen_twinfree_pieces, is_twinfree
from cycles_solver import Solver, g_piece

NMAX = 22
NPROC = 32

def build():
    pieces = gen_twinfree_pieces(NMAX)
    tf = [(n, e) for k, (n, e) in pieces.items() if is_twinfree(n, e)]
    tf = sorted(set((n, tuple(e)) for n, e in tf), key=lambda x: (-x[0], x[1]))
    return tf

def worker(shard):
    tf = build()
    npieces = len(tf)
    sol = Solver(cap=3_000_000)
    out = []
    for i in range(shard, npieces, NPROC):
        n, e = tf[i]
        g = g_piece(sol, n, e)
        E = n - 1
        out.append((n, e, g, (g > 1 or g % 2 != E % 2)))
    return shard, out, len(sol.memo), sol.clears

if __name__ == '__main__':
    t0 = time.time()
    tf = build()
    npieces = len(tf)
    print(f"total twin-free pieces <= {NMAX}: {npieces} ({time.time()-t0:.0f}s)", flush=True)
    with Pool(NPROC) as pool:
        results = pool.map(worker, list(range(NPROC)))
    allv = []
    for shard, out, mem, clears in sorted(results):
        allv.extend(out)
        print(f"shard {shard}: {len(out)} pieces, memo={mem}, clears={clears}", flush=True)
    viol = [x for x in allv if x[3]]
    import collections
    per_n = collections.Counter(n for n, e, g, v in allv)
    gdist = collections.Counter(g for n, e, g, v in allv)
    print(f"done in {time.time()-t0:.0f}s; violations: {len(viol)}", flush=True)
    print("per-n:", dict(sorted(per_n.items())), flush=True)
    print("g-dist:", dict(sorted(gdist.items())), flush=True)
    json.dump({"nmax": NMAX, "total": npieces,
               "pieces": [[n, list(e), g] for n, e, g, v in allv],
               "violations": [[n, list(e), g] for n, e, g, v in viol]},
              open('results_q114.json', 'w'))
