"""Heuristic local search for small AMRZ margin lambda+mu-n on connected graphs (diagnostic only).
usage: amrz_ls.py AMRZ_PY N SECONDS SEED TAG"""
import importlib.util
import json
import math
import os
import random
import sys
import time

spec = importlib.util.spec_from_file_location('amrz', sys.argv[1])
A = importlib.util.module_from_spec(spec)
spec.loader.exec_module(A)
N, SECS, SEED, TAG = int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
rng = random.Random(SEED)


def margin(adj):
    r = A.lam_mu(N, adj)
    if r is None:
        return None, None
    return r[0] + r[1] - N, r


def rand_graph(p):
    while True:
        adj = [0] * N
        for i in range(N):
            for j in range(i + 1, N):
                if rng.random() < p:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
        m, r = margin(adj)
        if m is not None:
            return adj, m, r


t0 = time.time()
best = (10 ** 9, None, None)
restarts = 0
hist = {}
while time.time() - t0 < SECS:
    restarts += 1
    adj, m, r = rand_graph(rng.choice([0.2, 0.3, 0.4, 0.5, 0.6, 0.7]))
    T = 2.0
    for step in range(3000):
        i, j = rng.sample(range(N), 2)
        adj[i] ^= 1 << j
        adj[j] ^= 1 << i
        m2, r2 = margin(adj)
        if m2 is not None and (m2 <= m or rng.random() < math.exp((m - m2) / T)):
            m, r = m2, r2
            if m < best[0]:
                best = (m, list(adj), r)
        else:
            adj[i] ^= 1 << j
            adj[j] ^= 1 << i
        T = max(0.05, T * 0.998)
    hist[m] = hist.get(m, 0) + 1
out = {'n': N, 'seed': SEED, 'restarts': restarts, 'best_margin': best[0], 'best_adj': best[1],
       'best_lambda_mu': best[2], 'final_margin_hist': {str(k): v for k, v in sorted(hist.items())},
       'seconds': round(time.time() - t0, 1), 'note': 'heuristic, not exhaustive'}
with open(os.path.join(A.OUT, f'ls-{TAG}.json'), 'x') as f:
    json.dump(out, f, indent=1)
print(json.dumps(out))
