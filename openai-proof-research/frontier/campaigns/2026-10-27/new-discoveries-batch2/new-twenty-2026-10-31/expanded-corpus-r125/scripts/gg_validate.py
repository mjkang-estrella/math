import sys, random, itertools
sys.path.insert(0, sys.argv[1])
from gg_lib import *
random.seed(int(sys.argv[2]))
bad = 0; cnt = 0
# all labeled graphs on <=6 vertices, recognizer vs brute definition
for n in range(1, 7):
    pairs = list(itertools.combinations(range(n), 2))
    step = 1 if n <= 5 else 7
    for e in range(0, 1 << len(pairs), step):
        adj = [0]*n
        for k, (a, b) in enumerate(pairs):
            if e >> k & 1: adj[a] |= 1 << b; adj[b] |= 1 << a
        full = (1 << n) - 1
        r = recog_perfect(adj, full); b = brute_perfect(adj, full); cnt += 1
        if r != b: bad += 1; print('MISMATCH', n, adj, r, b)
print('n<=6 checked', cnt, 'mismatches', bad, flush=True)
for t in range(400):
    n = random.choice([7, 8]); p = random.random()
    adj = [0]*n
    for a in range(n):
        for b in range(a+1, n):
            if random.random() < p: adj[a] |= 1 << b; adj[b] |= 1 << a
    full = (1 << n) - 1
    r = recog_perfect(adj, full); b = brute_perfect(adj, full); cnt += 1
    if r != b: bad += 1; print('MISMATCH', n, adj, r, b)
print('random 7-8 done; total', cnt, 'mismatches', bad)
